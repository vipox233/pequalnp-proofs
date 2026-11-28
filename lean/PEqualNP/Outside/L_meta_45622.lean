import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45622

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008241376 * 2 ^ 32 + 4001933440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x061b0b8610d66d81#64 ++ 0x100c36170c21acdb#64 ++ 0x8e3f1f8e31ffffff#64 ++ 0x7d1c7e3f1c63ffff#64 : BitVec 256),
   (0x30c565b0c62b16a0#64 ++ 0x00618acb618c562d#64 ++ 0x71c7e7f1ce3f1ff7#64 ++ 0xfee38fcfe39c7e3f#64 : BitVec 256),
   (0x8168b05bf031a310#64 ++ 0x2b02d160b7e06346#64 ++ 0x81f8f8fff031e3db#64 ++ 0xbb03f1f1ffe063c7#64 : BitVec 256),
   (0xda00fe016b41d808#64 ++ 0x47b401fc02d683b0#64 ++ 0xfe00ff01ffc1fc1d#64 ++ 0xdffc01fe03ff83f8#64 : BitVec 256),
   (0xedfe0001bdbc0004#64 ++ 0x8fdbfc00037b7800#64 ++ 0xffff0001fffe0061#64 ++ 0xeffffe0003fffc00#64 : BitVec 256),
   (0xffb7dfec00000002#64 ++ 0xf3ff6fbfd8000000#64 ++ 0xfffffffe00000001#64 ++ 0xf3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [8, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [8, 1]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x041a000010940000 0x0008340000212800 0x8e3f000031fe0061 0x6d1c7e000063fc00

def z1 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z2 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z3 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z4 : W := mkw 0xc800000129000000 0x0790000002520000 0xfe000001ffc00001 0xcffc000003ff8000

def z5 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z6 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffffffe00000001 0xf3fffffffc000000

def z7 : W := mkw 0x0168205ad0312310 0x2802d040b5a06246 0x01f8e0ffc03103d3 0xba03f1c1ff806207

def z8 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff0001fffe0061 0xeffffe0003fffc00

def z9 : W := mkw 0x35b745ec00000002 0xb06b6e8bd8000000 0x71ffe7fe00000001 0xf2e3ffcffc000000

def z10 : W := mkw 0xda01ffb16b43dea8 0x47b403ff62d687bd 0xfe00fff1ffc1ff9f 0xdffc01ffe3ff83ff

def z11 : W := mkw 0x000020016b41d808 0x0400004002d683b0 0x00000001ffc1fc1c 0x0c00000003ff83f8

def z12 : W := mkw 0x25b701ec00000002 0xb04b6e03d8000000 0x01ff00fe00000000 0x2003fe01fc000000

def z13 : W := mkw 0x06130b8400c64c81 0x100c261708018c99 0x0e07070001ce1c24 0x441c0e0e00039c38

def z14 : W := mkw 0x8120904800000000 0x2302412090000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z15 : W := mkw 0x00402010c0210200 0x0000804021804204 0x01c0e0f1c03103d3 0xba0381c1e3806207

def z16 : W := mkw 0xb1edf5fbf63bb7b0 0x2b63dbebf7ec776f 0xf1fffffffe3fffff 0xffe3fffffffc7fff

def z17 : W := mkw 0xa1ecb05bf439a310 0x2b43d960b7e87346 0xf1fff8fffe3fe3fb 0xffe3fff1fffc7fc7

def z18 : W := mkw 0x00482013fdbda314 0x0c00904027fb7b46 0x00000001ffffe3fa 0x0c00000003ffffc7

def z19 : W := mkw 0xf9a4d46800000002 0xe3f349a8d0000000 0x71c0e07000000000 0x82e381c0e0000000

def z20 : W := mkw 0xffbfdfee10d66d83 0xf3ff7fbfdc21acdb 0xfffffffe31ffffff 0xfffffffffc63ffff

def z21 : W := mkw 0x0413018400860481 0x1008260308010c09 0x00070000000e0020 0x00000e0000001c00

def z22 : W := mkw 0x5a006e016b41d808 0x44b400dc02d683b0 0x7e000701ffc1fc1c 0x4cfc000e03ff83f8

def z23 : W := mkw 0xffb7dfed29000002 0xf7ff6fbfda520000 0xffffffffffc00001 0xffffffffffff8000

def z24 : W := mkw 0x0000000000020480 0x0000000000000409 0x00000000003f1ff6 0x0c00000000007e3f

def z25 : W := mkw 0xedf60001adac0004 0x8fdbec00035b5800 0x7fc70001cfce0020 0xc6ff8e00039f9c00

def z26 : W := mkw 0x02000a0000404800 0x0004001400008090 0x8e001f0031c1fc1d 0x5d1c003e006383f8

def z27 : W := mkw 0xde1bff877bd7fd89 0x57bc37ff0ef7affb 0xfe3fff8fffffffff 0xfffc7fff1fffffff

def z28 : W := mkw 0xde1afe017bd5d808 0x47bc35fc02f7abb0 0xfe3fff01fffffc7d 0xfffc7ffe03fffff8

def z29 : W := mkw 0x81680001b0300000 0x0b02d00003606000 0x81f80001f0300041 0xab03f00003e06000

def z30 : W := mkw 0x7e974fa400000002 0xd0fd2e9f48000000 0x7e07070000000000 0x40fc0e0e00000000

def z31 : W := mkw 0xfffffffff031a312 0xfbffffffffe06346 0xfffffffff031e3db 0xfbffffffffe063c7

def z32 : W := mkw 0x0008000210102100 0x0000100004202042 0x8038188e3031e3db 0x390070311c6063c7

def z33 : W := mkw 0xefffbbdffdffef95 0xbfdfff77bffbffdf 0xffffffffffffffff 0xffffffffffffffff

def z34 : W := mkw 0x06130b8400000000 0x100c261708000000 0x8e3f1f8e00000001 0x711c7e3f1c000000

def z35 : W := mkw 0xf9e5f5f8c62b16a2 0xe3f3cbebf18c562d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z36 : W := mkw 0x8000b00160018000 0x0300016002c00300 0x8000f801f001e019 0x9b0001f003e003c0

def z37 : W := mkw 0xdb68fe5bfb71fb18 0x6fb6d1fcb7f6e3f6 0xfff8fffffff1ffdf 0xfffff1ffffffe3ff

def z38 : W := mkw 0x0001018000000000 0x0000020300000000 0x0007078000000001 0x70000e0f00000000

def z39 : W := mkw 0x31ed65fad63b37b0 0x2863dacbf5ac766f 0x71ffe7ffce3f1ff7 0xfee3ffcfff9c7e3f

def z40 : W := mkw 0xec9600012d8c0004 0x87d92c00025b1800 0xfe070001ffce0021 0xcffc0e0003ff9c00

def z41 : W := mkw 0xffffdfedb0300002 0xfbffffbfdb606000 0xfffffffff0300041 0xfbffffffffe06000

def z42 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x00000001f031e3da 0x0800000003e063c7

def z43 : W := mkw 0x25b6000000000000 0x804b6c0000000000 0x01ff000000000000 0x2003fe0000000000

def z44 : W := mkw 0x00480001bdbc0004 0x0c009000037b7800 0x00000001fffe0060 0x0c00000003fffc00

def z45 : W := mkw 0x25ff018694be2585 0x984bfe030d297c4b 0x01ff008e003e03e2 0x2003fe011c007c07

def z46 : W := mkw 0x0008000210d66d81 0x000010000421acdb 0x0000000031fffffe 0x0c0000000063ffff

def z47 : W := mkw 0x1001f5fa4203b7b0 0x202003ebf484076f 0x0000fffe0001ff9e 0x100001fffc0003ff

def z48 : W := mkw 0x0168005a90302310 0x2802d000b5206046 0x01f800fe003003c2 0x2003f001fc006007

def z49 : W := mkw 0xfe97ffa56b41d80a 0xd7fd2fff4ad683b0 0xfe07ff01ffc1fc1d 0xdffc0ffe03ff83f8

def z50 : W := mkw 0xedb6000000000000 0x83db6c0000000000 0xffff000000000001 0xe3fffe0000000000

def z51 : W := mkw 0xffffdfedbdbc0006 0xffffffbfdb7b7800 0xfffffffffffe0061 0xfffffffffffffc00

def z52 : W := mkw 0x061a0a0610d46901 0x100c34140c21a8d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z53 : W := mkw 0x8128904b3010a110 0x2b02512096602142 0x8038188e3031e3db 0x390070311c6063c7

def z54 : W := mkw 0x7e974fa400000002 0xd0fd2e9f48000000 0xfe3f1f8e00000001 0x71fc7e3f1c000000

def z55 : W := mkw 0xca000a0129404800 0x0794001402528090 0xfe001f01ffc1fc1d 0xdffc003e03ff83f8

def z56 : W := mkw 0x20c4000084280000 0x0041880001085000 0x71c70001ce3e0061 0xeee38e00039c7c00

def z57 : W := mkw 0x8160b058c0210200 0x2302c160b1804204 0x81f8f8ffc03103d3 0xbb03f1f1ff806207

def z58 : W := mkw 0x8160b059e0218210 0x2b02c160b3c04304 0x01c0e071c0000000 0x820381c0e3800000

def z59 : W := mkw 0x00402010c62b16a0 0x00008040218c562d 0x00000001ce3f1ff6 0x0c000000039c7e3f

def z60 : W := mkw 0x0168b05ad031a310 0x2802d160b5a06346 0x01f8f8fe0031e3da 0x3003f1f1fc0063c7

def z61 : W := mkw 0x00482013f0f7ef91 0x0800904027e1efdf 0x00000001f1fffffe 0x0c00000003e3ffff

def z62 : W := mkw 0x877bbbdff0f7ef91 0x3b0ef777bfe1efdf 0x8ffffffff1ffffff 0xff1fffffffe3ffff

def z63 : W := mkw 0xfff7fffde0218212 0xfbffeffffbc04304 0xffffffffc0000001 0xf3ffffffff800000

def z64 : W := mkw 0x1001658042031480 0x002002cb00840629 0x7007e781ce3f1ff7 0xfee00fcf039c7e3f

def z65 : W := mkw 0xe9e40001ad280004 0x8fd3c800035a5000 0x71c70001ce3e0061 0xeee38e00039c7c00

def z66 : W := mkw 0x0120004800000000 0x2002400090000000 0x01f800fe00000000 0x2003f001fc000000

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z68 : W := mkw 0xcf329a4c00000002 0xf39e653498000000 0x8ff8f8fe00000001 0xb31ff1f1fc000000

def z69 : W := mkw 0x20c4000084280000 0x0041880001085000 0x01c70000003e0060 0x20038e0000007c00

def z70 : W := mkw 0xc800b00169018000 0x0790016002d20300 0xfe00f801ffc1e019 0xdffc01f003ff83c0

def z71 : W := mkw 0x1201dfee00426d83 0x702403bfdc0084db 0x0000fffe0001ff9e 0x100001fffc0003ff

def z72 : W := mkw 0x1000640042011000 0x002000c800840220 0x7000e701ce011c15 0xdee001ce039c0238

def z73 : W := mkw 0x9321dfec00000002 0x732643bfd8000000 0x81f8fffe00000001 0xb303f1fffc000000

def z74 : W := mkw 0x8160b05be021a310 0x2b02c160b7c04346 0x01c0f8ffc001e39a 0x920381f1ff8003c7

def z75 : W := mkw 0xfdfed469bdbc0006 0xeffbfda8d37b7800 0xffffe071fffe0061 0xefffffc0e3fffc00

def z76 : W := mkw 0x8168b05bfdbda314 0x2f02d160b7fb7b46 0x81f8f8ffffffe3fb 0xbf03f1f1ffffffc7

def z77 : W := mkw 0x81682013f031a310 0x0b02d04027e06346 0x81f80001f031e3db 0xab03f00003e063c7

def z78 : W := mkw 0xda00de0000404800 0x43b401bc00008090 0xfe00ff0031c1fc1d 0xdffc01fe006383f8

def z79 : W := mkw 0x308545a000000000 0x00610a8b40000000 0x71c7e7f000000001 0xf2e38fcfe0000000

def z80 : W := mkw 0x8128904b3010a110 0x2b02512096602142 0x8038180e3000e008 0x010070301c6001c0

def z81 : W := mkw 0x81682011f0310200 0x0b02d04023e06204 0x81f8e0f1f03103d3 0xbb03f1c1e3e06207

def z82 : W := mkw 0x0000b05a4001a310 0x20000160b4800346 0x0000f8fe0001e39a 0x100001f1fc0003c7

def z83 : W := mkw 0xffb6de6c00000002 0xf3ff6dbcd8000000 0xfff8f87e00000000 0x83fff1f0fc000000

def z84 : W := mkw 0xffb7dfec00404802 0xf3ff6fbfd8008090 0xfffffffe31c1fc1d 0xfffffffffc6383f8

def z85 : W := mkw 0x061a0a0610d46901 0x100c34140c21a8d2 0x8e3f180e31fee069 0x6d1c7e301c63fdc0

def z86 : W := mkw 0xcf329a4c00000002 0xf39e653498000000 0x8e38180e00000000 0x011c70301c000000

def z87 : W := mkw 0x0048001290302310 0x0800900025206046 0x00000000003003c2 0x0000000000006007

def z88 : W := mkw 0xa5feb05bf4bda314 0xab4bfd60b7e97b46 0x81fff8fff03fe3fb 0xbb03fff1ffe07fc7

def z89 : W := mkw 0x308545a0060a14a0 0x00610a8b400c1429 0x700707000e0e1c24 0x44e00e0e001c1c38

def z90 : W := mkw 0xefff0b87bdfe6d85 0x9fdffe170f7bfcdb 0xffff1f8fffffffff 0xfffffe3f1fffffff

def z91 : W := mkw 0x4a000a0009404808 0x4494001400128090 0x0e00000001c00000 0x001c000000038000

def z92 : W := mkw 0x00482013f63bb7b0 0x0800904027ec776f 0x00000001fe3ffffe 0x0c00000003fc7fff

def z93 : W := mkw 0x12016fb642437fa1 0x102402df6c8486ff 0x0000fffe0001ff9e 0x100001fffc0003ff

def z94 : W := mkw 0x30c565b0c6291220 0x00618acb618c5224 0x71c7e7f1ce000001 0xf2e38fcfe39c0000

def z95 : W := mkw 0xb0c5f5b1e62b96a0 0x03618beb63cc572d 0xf1c7fff1fe3fffff 0xffe38fffe3fc7fff

def z96 : W := mkw 0xdb20de4800000000 0x63b641bc90000000 0xfff8fffe00000001 0xf3fff1fffc000000

def z97 : W := mkw 0xedfeb05bfdbda314 0xafdbfd60b7fb7b46 0xfffff8ffffffe3fb 0xfffffff1ffffffc7

def z98 : W := mkw 0x000800033010a110 0x0800100006602142 0x000000003000e008 0x00000000006001c0

def z99 : W := mkw 0xda00de0000000000 0x43b401bc00000000 0xfe00ff0000000001 0xd3fc01fe00000000

def z100 : W := mkw 0x20c42010c62b16a0 0x00418840218c562d 0x71c70001ce3f1ff7 0xeee38e00039c7e3f

def z101 : W := mkw 0x06120a0400c44801 0x100c241408018890 0x0e00000001c00000 0x001c000000038000

def z102 : W := mkw 0x061b0b8410d64c81 0x100c36170821ac99 0x8e3f070031fe1c65 0x6d1c7e0e0063fc38

def z103 : W := mkw 0xf9a4f4696b01900a 0xe7f349e8d2d60320 0x71c0e071ce000000 0x82e381c0e39c0000

def z104 : W := mkw 0xe9ecb05bfd39a314 0xafd3d960b7fa7346 0xf1f8f8fffe31e3db 0xbbe3f1f1fffc63c7

def z105 : W := mkw 0x873b9bcf30d6ed91 0x3b0e77379e61addb 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z106 : W := mkw 0x8168b05bf63bb7b0 0x2b02d160b7ec776f 0x81f8f8fffe3fffff 0xbf03f1f1fffc7fff

def z107 : W := mkw 0x9200fe016241d808 0x432401fc02c483b0 0x8000ff01f001fc1d 0x9b0001fe03e003f8

def z108 : W := mkw 0x81680003b0302100 0x0b02d00007606042 0x81f8188ff031e3db 0xbb03f0311fe063c7

def z109 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x8038188ff031e3db 0x390070311fe063c7

def z110 : W := mkw 0x06130b8400c64c81 0x100c261708018c99 0x8e071f0031cffc3d 0x5d1c0e3e00639ff8

def z111 : W := mkw 0x8120000000000000 0x0302400000000000 0x81f8000000000001 0xa303f00000000000

def z112 : W := mkw 0x6c9600000d8c0004 0x84d92c00001b1800 0x7e0700000fce0020 0x44fc0e00001f9c00

def z113 : W := mkw 0x30c545b0842a06a0 0x00618a8b6108540d 0x71c7e7f0003e03e3 0xf2e38fcfe0007c07

def z114 : W := mkw 0xedf60001ad280004 0x8fdbec00035a5000 0xffff0001ce000001 0xe3fffe00039c0000

def z115 : W := mkw 0x32c5fffcc62b16a2 0x70658bfff98c562d 0x71c7ffffce3f1ff7 0xfee38fffff9c7e3f

def z116 : W := mkw 0x00400010842a06a0 0x000080002108540d 0x00000000003e03e2 0x0000000000007c07

def z117 : W := mkw 0x7fb74fec00000002 0xf0ff6e9fd8000000 0x7fff07fe00000000 0x60fffe0ffc000000

def z118 : W := mkw 0x36974fa400000000 0x106d2e9f48000000 0xfffffffe00000001 0xf3fffffffc000000

def z119 : W := mkw 0x36df6fb6d6ff7fa1 0x106dbedf6dadfeff 0xffffffffffffffff 0xffffffffffffffff

def z120 : W := mkw 0x3084442000000000 0x0061088840000000 0x71c0e07000000000 0x82e381c0e0000000

def z121 : W := mkw 0x1613dfec00000002 0x702c27bfd8000000 0x8e3ffffe00000001 0x711c7ffffc000000

def z122 : W := mkw 0xedfe2011ffbf16a4 0x8fdbfc4023ff7e2d 0xffff0001ffff1ff7 0xeffffe0003fffe3f

def z123 : W := mkw 0x0009018210d66d81 0x000012030421acdb 0x0007078031ffffff 0x7c000e0f0063ffff

def z124 : W := mkw 0x065b2b97f0f7ef91 0x180cb6572fe1efdf 0x8e3f1f8ff1ffffff 0x7d1c7e3f1fe3ffff

def z125 : W := mkw 0xedfe2013fdbda314 0x8fdbfc4027fb7b46 0xffff0001ffffe3fb 0xeffffe0003ffffc7

def z126 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x01f8e0ffc03003c2 0xa203f1c1ff806007

def z127 : W := mkw 0x30c545a084280000 0x00618a8b41085000 0x71c7e7f1ce3e0061 0xfee38fcfe39c7c00

def z128 : W := mkw 0x00482012d0312300 0x0000904025a06246 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z129 : W := mkw 0x00402010c0210200 0x0000804021804204 0x01c0e071c0000000 0x820381c0e3800000

def z130 : W := mkw 0x0040000080200000 0x0000800001004000 0x01c00001c0300041 0xaa03800003806000

def z131 : W := mkw 0x8128b05b7011a310 0x2b025160b6e02346 0x8038f8fe3001e39a 0x110071f1fc6003c7

def z132 : W := mkw 0x041b018610962581 0x100836030c212c4b 0x003f008e003e03e2 0x20007e011c007c07

def z133 : W := mkw 0x20c501b0842a06a0 0x00418a036108540d 0x01c700f0003e03e2 0x20038e01e0007c07

def z134 : W := mkw 0x30c46430c6291220 0x006188c8618c5224 0x71c0e0f1ce3103d3 0xbae381c1e39c6207

def z135 : W := mkw 0xedff0187bdbe2585 0x9fdbfe030f7b7c4b 0xffff008ffffe03e3 0xeffffe011ffffc07

def z136 : W := mkw 0xefff0b85bdbc0004 0x9fdffe170b7b7800 0xffff1f8ffffe0061 0xfffffe3f1ffffc00

def z137 : W := mkw 0xda00fe016b019008 0x47b401fc02d60320 0xfe00ff01ce000001 0xd3fc01fe039c0000

def z138 : W := mkw 0x100165b0420316a0 0x002002cb6084062d 0x0000e7f000011f96 0x100001cfe000023f

def z139 : W := mkw 0x1200fe004241d808 0x402401fc008483b0 0x0000ff000001fc1c 0x100001fe000003f8

def z140 : W := mkw 0xdb20fe496b41d808 0x67b641fc92d683b0 0xfff8ffffffc1fc1d 0xfffff1ffffff83f8

def z141 : W := mkw 0x30c545b0862a16a0 0x00618a8b610c542d 0x71c707f00e3e1fe6 0x64e38e0fe01c7c3f

def z142 : W := mkw 0x6c9e00001d9c0004 0x84d93c00003b3800 0xfe3f00003ffe0061 0x6dfc7e00007ffc00

def z143 : W := mkw 0x0000005a00002310 0x20000000b4000046 0x000000fe00000382 0x00000001fc000007

def z144 : W := mkw 0x1201fffe4001a312 0x702403fffc800346 0x0000fffe0001e39a 0x100001fffc0003c7

def z145 : W := mkw 0x25fe000094bc0004 0x884bfc0001297800 0x01ff0000003e0060 0x2003fe0000007c00

def z146 : W := mkw 0xfac5ffb1ef6bdea8 0x47f58bff63ded7bd 0xffc7fff1ffffffff 0xffff8fffe3ffffff

def z147 : W := mkw 0x7c9745a00f8e14a4 0x84f92e8b401f1c29 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z148 : W := mkw 0xffb7ffed6b41d80a 0xf7ff6fffdad683b0 0xffffffffffc1fc1d 0xffffffffffff83f8

def z149 : W := mkw 0x25fe000094bc0004 0x884bfc0001297800 0x8fff000031fe0061 0x6d1ffe000063fc00

def z150 : W := mkw 0x000101b0000206a0 0x000002036000040d 0x000000f000000382 0x00000001e0000007

def z151 : W := mkw 0x0048b05bf031a310 0x28009160b7e06346 0x0000f8fff031e3da 0x180001f1ffe063c7

def z152 : W := mkw 0xda01ffed6b41d80a 0x77b403ffdad683b0 0xfe00ffffffc1fc1d 0xdffc01ffffff83f8

def z153 : W := mkw 0xfedfffb7ffffffa9 0x57fdbfff6fffffff 0xffffffffffffffff 0xffffffffffffffff

def z154 : W := mkw 0x20c4003084280220 0x0041880061085004 0x01c0007000000000 0x00038000e0000000

def z155 : W := mkw 0x0168005a90302310 0x2802d000b5206046 0x81f818fe3031e3db 0x3903f031fc6063c7

def z156 : W := mkw 0xdf33dfec00000002 0xf3be67bfd8000000 0x8e38fffe00000000 0x111c71fffc000000

def z157 : W := mkw 0x25ff01ec94bc0006 0xb84bfe03d9297800 0x01ff00fe003e0060 0x2003fe01fc007c00

def z158 : W := mkw 0xf9a4d46800000002 0xe3f349a8d0000000 0xf1f8f8fe00000001 0xb3e3f1f1fc000000

def z159 : W := mkw 0xfff7fffcc62b16a2 0xf3ffeffff98c562d 0xffffffffce3f1ff7 0xffffffffff9c7e3f

def z160 : W := mkw 0x1200fe5a4241fb18 0x602401fcb48483f6 0x0000fffe0001ff9e 0x100001fffc0003ff

def z161 : W := mkw 0xffb7dfec0d8c0006 0xf7ff6fbfd81b1800 0xfffffffe0fce0021 0xf7fffffffc1f9c00

def z162 : W := mkw 0xedfe9049bdbc0004 0xafdbfd20937b7800 0xfffff8fffffe0061 0xfffffff1fffffc00

def z163 : W := mkw 0xffb7dfec00c64c83 0xf3ff6fbfd8018c99 0xfffffffe01ce1c25 0xf7fffffffc039c38

def z164 : W := mkw 0xca00ba016941c808 0x4794017402d28390 0x8e00f801f1c1e019 0x9b1c01f003e383c0

def z165 : W := mkw 0xfdb6d46800000002 0xe3fb6da8d0000000 0xffffe07000000001 0xe3ffffc0e0000000

def z166 : W := mkw 0xffb7dfed2940c80a 0xf7ff6fbfda528190 0xfffffffe31c0e009 0xf3fffffffc6381c0

def z167 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x01c7e7f0003f1ff6 0x30038fcfe0007e3f

def z168 : W := mkw 0x8120b04960018000 0x2302416092c00300 0x81f8f8fff001e019 0xbb03f1f1ffe003c0

def z169 : W := mkw 0xcd3a000139940004 0x8f9a740002732800 0x8e38000031c00000 0x011c700000638000

def z170 : W := mkw 0xfdff65b1ffbf16a4 0x8ffbfecb63ff7e2d 0xffffe7f1ffff1ff7 0xffffffcfe3fffe3f

def z171 : W := mkw 0xffffdfec94bc0006 0xfbffffbfd9297800 0xfffffffe003e0061 0xf3fffffffc007c00

def z172 : W := mkw 0xedfe2011fdbd0204 0x8fdbfc4023fb7a04 0xffffe0f1ffff03f3 0xffffffc1e3fffe07

def z173 : W := mkw 0xedb6904800000000 0xa3db6d2090000000 0xfffff8fe00000001 0xf3fffff1fc000000

def z174 : W := mkw 0x24960000048c0004 0x80492c0000091800 0x00070000000e0020 0x00000e0000001c00

def z175 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x70070701ce3f1ff6 0x4ce00e0e039c7e3f

def z176 : W := mkw 0xfff7dffc842a06a2 0xf3ffefbff908540d 0xfffffffe003e03e3 0xf3fffffffc007c07

def z177 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0x7000ff01ce01fc1c 0x92e001fe039c03f8

def z178 : W := mkw 0xd800f4016b019008 0x47b001e802d60320 0xf000f801fe01e019 0x9be001f003fc03c0

def z179 : W := mkw 0xfff7fffcc0210202 0xf3ffeffff9804204 0xffffffffc03103d3 0xfbffffffff806207

def z180 : W := mkw 0xce1b0b8739d66d81 0x179c36170e73acdb 0xfe3f1f8fffffffff 0xfffc7e3f1fffffff

def z181 : W := mkw 0xffbfdfed39940006 0xffff7fbfda732800 0xfffffffe31c00001 0xf3fffffffc638000

def z182 : W := mkw 0xffb7dfec0b40580a 0xf7ff6fbfd81680b0 0xfffffffe0fc01c05 0xf7fffffffc1f8038

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x8038188e00000001 0x310070311c000000

def z184 : W := mkw 0xb1e5f5f8c62b16a0 0x2363cbebf18c562d 0xf1ffffffce3f1ff7 0xffe3ffffff9c7e3f

def z185 : W := mkw 0xc800000129000000 0x0790000002520000 0x70000001ce000000 0x82e00000039c0000

def z186 : W := mkw 0x00000000060a14a0 0x00000000000c1429 0x000000000e0e1c24 0x04000000001c1c38

def z187 : W := mkw 0xedfe005bbdbc2314 0xafdbfc00b77b7846 0xffff00fffffe03e3 0xeffffe01fffffc07

def z188 : W := mkw 0x06120a0400000000 0x100c241408000000 0x8e38180e00000000 0x011c70301c000000

def z189 : W := mkw 0xcd3a000139940004 0x8f9a740002732800 0xfe380001ffc00001 0xcffc700003ff8000

def z190 : W := mkw 0xca009a0000000000 0x4394013400000000 0x8e00180000000000 0x011c003000000000

def z191 : W := mkw 0x30cd65b3f63bb7b0 0x08619acb67ec776f 0x71c7e7f1fe3fffff 0xfee38fcfe3fc7fff

def z192 : W := mkw 0xfffefe01fffdd80c 0xcffffdfc03fffbb0 0xffffff01fffffc7d 0xfffffffe03fffff8

def z193 : W := mkw 0x3084442006081020 0x00610888400c1020 0x700000000e000000 0x00e00000001c0000

def z194 : W := mkw 0x00402010c6291220 0x00008040218c5224 0x00000001ce000000 0x00000000039c0000

def z195 : W := mkw 0x30c46430c6291220 0x006188c8618c5224 0x71c7e071ce3e0061 0xeee38fc0e39c7c00

def z196 : W := mkw 0x053a000010940004 0x880a740000212800 0x0038000000000000 0x0000700000000000

def z197 : W := mkw 0x0008000210102100 0x0000100004202042 0x0038008e003003c2 0x200070011c006007

def z198 : W := mkw 0x5a004e000b405808 0x44b4009c001680b0 0xfe001f003fc1fc1d 0x5dfc003e007f83f8

def z199 : W := mkw 0x1000f40042019008 0x402001e800840320 0x0000e00000000000 0x000001c000000000

def z200 : W := mkw 0xe9e40001ad280004 0x8fd3c800035a5000 0x71c00001ce000000 0x82e38000039c0000

def z201 : W := mkw 0x02010b8600426d81 0x100402170c0084db 0x00001f8e0001ff9e 0x1000003f1c0003ff

def z202 : W := mkw 0x8040b011e0218200 0x0300816023c04304 0x81c0f8f1f031e3db 0xbb0381f1e3e063c7

def z203 : W := mkw 0x249701a400000002 0x90492e0348000000 0x0007000000000000 0x00000e0000000000

def z204 : W := mkw 0xffb7ffed6b01900a 0xf7ff6fffdad60320 0xffffffffce000001 0xf3ffffffff9c0000

def z205 : W := mkw 0x8000000120000000 0x0300000002400000 0x80000001f0000001 0x8b00000003e00000

def z206 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe00f801ffc0e008 0x83fc01f003ff81c0

def z207 : W := mkw 0x1000643042011220 0x002000c860840224 0x0000e07000000000 0x000001c0e0000000

def z208 : W := mkw 0x0000000200002100 0x0000000004000042 0x0000188e0001e39a 0x100000311c0003c7

def z209 : W := mkw 0xfba4de6800000002 0xe3f749bcd0000000 0xffc0ff7000000001 0xd3ff81fee0000000

def z210 : W := mkw 0x0009018210122580 0x000012030420244b 0x803f1f8e303fffff 0x7d007e3f1c607fff

def z211 : W := mkw 0xffb7dfec060a14a2 0xf3ff6fbfd80c1429 0xfffffffe0e0e1c25 0xf7fffffffc1c1c38

def z212 : W := mkw 0x0040000084280000 0x0000800001085000 0x00000001ce3e0060 0x0c000000039c7c00

def z213 : W := mkw 0x100064016b41d808 0x042000c802d683b0 0x7000e701ffc1fc1d 0xdee001ce03ff83f8

def z214 : W := mkw 0xde13df8400000000 0x53bc27bf08000000 0xfe3fff8e00000001 0xf3fc7fff1c000000

def z215 : W := mkw 0x8160b059e0218210 0x2b02c160b3c04304 0x81c0f871f001e019 0x9b0381f0e3e003c0

def z216 : W := mkw 0xda01ff876b43fd89 0x57b403ff0ed687fb 0xfe00ff8fffc1ff9f 0xdffc01ff1fff83ff

def z217 : W := mkw 0x5a004e000b405808 0x44b4009c001680b0 0x7e0007000fc01c04 0x44fc000e001f8038

def z218 : W := mkw 0xffffdffe90302312 0xfbffffbffd206046 0xfffffffe003003c3 0xf3fffffffc006007

def z219 : W := mkw 0x6cde0001bdbc0004 0x8cd9bc00037b7800 0x7e070001fffe0060 0x4cfc0e0003fffc00

def z220 : W := mkw 0x0001018000020480 0x0000020300000409 0x0000078000011f96 0x1000000f0000023f

def z221 : W := mkw 0xfffefe5bfffdfb1c 0xeffffdfcb7fffbf6 0xffffffffffffffff 0xffffffffffffffff

def z222 : W := mkw 0x8120904800000000 0x2302412090000000 0x01c0e07000000000 0x820381c0e0000000

def z223 : W := mkw 0x1201dfec00000002 0x702403bfd8000000 0x0000fffe00000000 0x100001fffc000000

def z224 : W := mkw 0xd800f4016b019008 0x47b001e802d60320 0x7000e001ce000000 0x82e001c0039c0000

def z225 : W := mkw 0x104165b0c22316a0 0x002082cb6184462d 0x01c0e7f1c0311fd7 0xba0381cfe380623f

def z226 : W := mkw 0xedb701ec00000002 0xb3db6e03d8000000 0xffff00fe00000001 0xe3fffe01fc000000

def z227 : W := mkw 0xf9e46431ef291224 0x8ff3c8c863de5224 0x71c0e071ce000000 0x82e381c0e39c0000

def z228 : W := mkw 0x1201ff864243fd89 0x502403ff0c8487fb 0x0000ff8e0001ff9e 0x100001ff1c0003ff

def z229 : W := mkw 0xfba4fe696b41d80a 0xe7f749fcd2d683b0 0xffc0ff71ffc1fc1d 0xdfff81fee3ff83f8

def z230 : W := mkw 0xcd7a0001bdbc0004 0x8f9af400037b7800 0x8e380001fffe0060 0x0d1c700003fffc00

def z231 : W := mkw 0x0000904800000000 0x2000012090000000 0x0000f8fe00000000 0x100001f1fc000000

def z232 : W := mkw 0x00402011e0218210 0x0800804023c04304 0x00000001c0000000 0x0000000003800000

def z233 : W := mkw 0x0048000094bc0004 0x0800900001297800 0x00000000003e0060 0x0000000000007c00

def z234 : W := mkw 0xcd7a0001b9b40004 0x8f9af40003736800 0x8ff80001f1f00041 0xab1ff00003e3e000

def z235 : W := mkw 0x308565a0460b14a0 0x00610acb408c1629 0x7007e701ce0f1c35 0xdee00fce039c1e38

def z236 : W := mkw 0x7e964e000fcc580c 0xc4fd2c9c001f98b0 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z237 : W := mkw 0x32c5ffb0c66bdea8 0x40658bff618cd7bd 0x71c7fff1ce3fffff 0xfee38fffe39c7fff

def z238 : W := mkw 0x061b2b877bd7fd89 0x140c36570ef7affb 0x8e3f1f8fffffffff 0x7d1c7e3f1fffffff

def z239 : W := mkw 0x30c46430c6291220 0x006188c8618c5224 0x71c0e071ce000000 0x82e381c0e39c0000

def z240 : W := mkw 0x00482012d6ff7fa1 0x0000904025adfeff 0x00000001fffffffe 0x0c00000003ffffff

def z241 : W := mkw 0xca009a012940c808 0x4794013402528190 0x8e00180031c0e008 0x011c0030006381c0

def z242 : W := mkw 0x1201ffb04243dea8 0x402403ff608487bd 0x0000fff00001ff9e 0x100001ffe00003ff

def z243 : W := mkw 0xd960f459eb219218 0x6fb2c1e8b3d64324 0x71c0e071ce000000 0x82e381c0e39c0000

def z244 : W := mkw 0x0168000090300000 0x0802d00001206000 0x01f8000000300040 0x2003f00000006000

def z245 : W := mkw 0xedfe904bbdbca114 0xafdbfd20977b7942 0xffff180ffffee069 0xeffffe301ffffdc0

def z246 : W := mkw 0xfbedfffbff7bffb8 0x6ff7dbfff7fef7ff 0xffffffffffffffff 0xffffffffffffffff

def z247 : W := mkw 0xfe97dfa400000002 0xd3fd2fbf48000000 0xfe07ff0000000001 0xd3fc0ffe00000000

def z248 : W := mkw 0xedfe0001b0300000 0x8bdbfc0003606000 0xffff0001f0300041 0xebfffe0003e06000

def z249 : W := mkw 0x061bbbde50d7ef91 0x300c3777bca1afdf 0x8e3ffffe31ffffff 0x7d1c7ffffc63ffff

def z250 : W := mkw 0x8168b059f0318210 0x2b02d160b3e06304 0x81f8e071f0300041 0xab03f1c0e3e06000

def z251 : W := mkw 0x1000440000000000 0x0020008800000000 0x7000e70000000001 0xd2e001ce00000000

def z252 : W := mkw 0x30cd65b2d63b37a0 0x00619acb65ac766f 0xf1fffffffe3fffff 0xffe3fffffffc7fff

def z253 : W := mkw 0x061a0a0610d66d81 0x100c34140c21acdb 0x8e38180e31fffffe 0x0d1c70301c63ffff

def z254 : W := mkw 0x24de000094bc0000 0x0049bc0001297800 0xffff0001fffe0061 0xeffffe0003fffc00

def z255 : W := mkw 0xc920000129000004 0x8f92400002520000 0x0000000000000000 0x0000000000000000

def z256 : W := mkw 0x6cd600008dac0004 0x84d9ac00011b5800 0x7fc70001cffe0061 0xeeff8e00039ffc00

def z257 : W := mkw 0x061b0b8610d46901 0x100c36170c21a8d2 0x8e3f1f8e31c0e009 0x711c7e3f1c6381c0

def z258 : W := mkw 0x21a4006800000002 0xa0434800d0000000 0x01c0007000000000 0x00038000e0000000

def z259 : W := mkw 0x02080a0210506900 0x000410140420a0d2 0x8e381f8e31f1ffdf 0x7d1c703f1c63e3ff

def z260 : W := mkw 0x8000b0016b41d808 0x0700016002d683b0 0x8000f801ffc1fc1d 0x9f0001f003ff83f8

def z261 : W := mkw 0x8000b05b6001a310 0x23000160b6c00346 0x8000f8fff001e39b 0x9b0001f1ffe003c7

def z262 : W := mkw 0xda00fe004241d808 0x43b401fc008483b0 0xfe00ff000001fc1d 0xd3fc01fe000003f8

def z263 : W := mkw 0x8168904bb030a110 0x2b02d12097606142 0x81f8180ff030e049 0xab03f0301fe061c0

def z264 : W := mkw 0xfffe4e01bffc580c 0xcffffc9c037ff8b0 0xffff0701fffe1c65 0xeffffe0e03fffc38

def z265 : W := mkw 0xc800000000000000 0x0390000000000000 0xfe00000000000001 0xc3fc000000000000

def z266 : W := mkw 0x057b01de90b62791 0x380af603bd216c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z267 : W := mkw 0xb1e5f5f9e62b96b0 0x2b63cbebf3cc572d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z268 : W := mkw 0xedf6000084280000 0x83dbec0001085000 0xffff0001ce3e0061 0xeffffe00039c7c00

def z269 : W := mkw 0x81689049b0300000 0x2b02d12093606000 0x81f8f8fff0300041 0xbb03f1f1ffe06000

def z270 : W := mkw 0xde13ff856bc7dc89 0x57bc27ff0ad78fb9 0xfe07ff01ffcffc3d 0xdffc0ffe03ff9ff8

def z271 : W := mkw 0x21e4000084280004 0x8843c80001085000 0x01c0000000000000 0x0003800000000000

def z272 : W := mkw 0xdb28fe4b7b51f918 0x6fb651fc96f6a3f2 0xfe38ff0fffc1fc1d 0xdffc71fe1fff83f8

def z273 : W := mkw 0x02009a000040c808 0x4004013400008190 0x000018000000e008 0x00000030000001c0

def z274 : W := mkw 0x208501a000000000 0x00410a0340000000 0x01c700f000000000 0x20038e01e0000000

def z275 : W := mkw 0x041b018610962581 0x100836030c212c4b 0x003f078e003f1ff7 0x7c007e0f1c007e3f

def z276 : W := mkw 0xda00fe0042011000 0x43b401fc00840220 0xfe00ff01ce011c15 0xdffc01fe039c0238

def z277 : W := mkw 0x02010b8400000000 0x1004021708000000 0x00001f8e00000000 0x1000003f1c000000

def z278 : W := mkw 0x1000440002001000 0x0020008800040020 0x700007000e001c04 0x44e0000e001c0038

def z279 : W := mkw 0x06130b8400c64c81 0x100c261708018c99 0x8e3f1f8e01ce1c25 0x751c7e3f1c039c38

def z280 : W := mkw 0x02000a0000404800 0x0004001400008090 0x0e00070001c01c04 0x441c000e00038038

def z281 : W := mkw 0xdb60fe59eb61da18 0x6fb6c1fcb3d6c3b4 0xffc0ff71ffc1fc1d 0xdfff81fee3ff83f8

def z282 : W := mkw 0x00482013fb71fb18 0x0c00904027f6e3f6 0x00000001fff1ffde 0x0c00000003ffe3ff

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x01c0e0f000000001 0xb20381c1e0000000

def z284 : W := mkw 0xda40fe11ef6bdea8 0x47b481fc23ded7bd 0xfe00ff01ffffffff 0xdffc01fe03ffffff

def z285 : W := mkw 0x077b0bde90f66f91 0x380ef617bd21ecdf 0x8fff1ffe31ffffff 0x7d1ffe3ffc63ffff

def z286 : W := mkw 0xfa85dfa000000000 0x43f50bbf40000000 0xffc7fff000000001 0xf3ff8fffe0000000

def z287 : W := mkw 0xfff7fffcc6291222 0xf3ffeffff98c5224 0xffffffffce000001 0xf3ffffffff9c0000

def z288 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c7e0f1ce3e03e2 0xa2e38fc1e39c7c07

def z289 : W := mkw 0x30c46400c6291000 0x006188c8018c5220 0x71c7e701ce3f1c75 0xfee38fce039c7e38

def z290 : W := mkw 0xcf3a9a0139d4c80c 0xcf9e75340273a990 0x8e38180031c0e008 0x011c7030006381c0

def z291 : W := mkw 0x0001018600022581 0x100002030c00044b 0x0000008e00000382 0x000000011c000007

def z292 : W := mkw 0xdf3afe017bd5d80c 0xcfbe75fc02f7abb0 0xfe38ff01ffc1fc1d 0xdffc71fe03ff83f8

def z293 : W := mkw 0x20c42010c4290200 0x0041884021885204 0x71c7e0f1ce3f03f3 0xfee38fc1e39c7e07

def z294 : W := mkw 0xda01ff816b43dc88 0x47b403ff02d687b9 0xfe07ff81ffffffff 0xfffc0fff03ffffff

def z295 : W := mkw 0xfdff45a1bfbe14a4 0x8ffbfe8b437f7c29 0xffff0701fffe1c65 0xeffffe0e03fffc38

def z296 : W := mkw 0x1000640042011000 0x002000c800840220 0x0000e70000011c14 0x100001ce00000238

def z297 : W := mkw 0x000020124001a310 0x0000004024800346 0x000000000001e39a 0x00000000000003c7

def z298 : W := mkw 0x041b018610962581 0x100836030c212c4b 0x8e3f008e31fe03e3 0x6d1c7e011c63fc07

def z299 : W := mkw 0xfa85ffa16b41d808 0x47f50bff42d683b0 0xffc7fff1ffc1fc1d 0xffff8fffe3ff83f8

def z300 : W := mkw 0xcc1a000139940000 0x0798340002732800 0xfe3f0001fffe0061 0xeffc7e0003fffc00

def z301 : W := mkw 0x26df0bb694fe6fa1 0x104dbe176d29fcdf 0x8fff1ffe31ffffff 0x7d1ffe3ffc63ffff

def z302 : W := mkw 0x8128904a10102100 0x2302512094202042 0x81f8f8fe3031e3db 0xbb03f1f1fc6063c7

def z303 : W := mkw 0xa1edb1fbf43ba7b0 0x2b43db63f7e8774f 0x81fff8fff03fe3fb 0xbb03fff1ffe07fc7

def z304 : W := mkw 0xffbfdfec10940002 0xf3ff7fbfd8212800 0xfffffffe31fe0061 0xfffffffffc63fc00

def z305 : W := mkw 0xedfe0003bdbc2104 0x8fdbfc00077b7842 0xffff188fffffe3fb 0xfffffe311fffffc7

def z306 : W := mkw 0xedb6000129000000 0x87db6c0002520000 0xffff0001ffc00001 0xeffffe0003ff8000

def z307 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81f8f87ff000e008 0x8303f1f0ffe001c0

def z308 : W := mkw 0xffb7ffed60018002 0xf3ff6fffdac00300 0xfffffffff001e019 0xfbffffffffe003c0

def z309 : W := mkw 0xdb68fe5bf031a310 0x6bb6d1fcb7e06346 0xfff8fffff031e3db 0xfbfff1ffffe063c7

def z310 : W := mkw 0x7e974fa4060a14a2 0xd0fd2e9f480c1429 0x7e0707000e0e1c24 0x44fc0e0e001c1c38

def z311 : W := mkw 0xa5ffb1fff031a312 0xbb4bff63ffe06346 0x81fff8fff031e3db 0xbb03fff1ffe063c7

def z312 : W := mkw 0xffff6fb7ffff7fa5 0x9ffffedf6ffffeff 0xffffffffffffffff 0xffffffffffffffff

def z313 : W := mkw 0xffffffedfffdd80e 0xffffffffdbfffbb0 0xfffffffffffffc7d 0xfffffffffffffff8

def z314 : W := mkw 0x24df01b694be27a1 0x1049be036d297c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z315 : W := mkw 0xca009a012940c808 0x4794013402528190 0x8e001f0031c1fc1d 0x5d1c003e006383f8

def z316 : W := mkw 0xcf339bcc00000002 0xf39e673798000000 0x8e3f1f8e00000001 0x711c7e3f1c000000

def z317 : W := mkw 0xedfe0003bdfe6d85 0x8fdbfc00077bfcdb 0xffff0001ffffffff 0xeffffe0003ffffff

def z318 : W := mkw 0x02090b8610d66d81 0x100412170c21acdb 0x00001f8e31fffffe 0x1c00003f1c63ffff

def z319 : W := mkw 0x20c501b0842a06a0 0x00418a036108540d 0x01c707f0003f1ff7 0x7c038e0fe0007e3f

def z320 : W := mkw 0xfff7fffdef6bdeaa 0xf7ffeffffbded7bd 0xffffffffffffffff 0xffffffffffffffff

def z321 : W := mkw 0x9368fe5bf271fb18 0x6b26d1fcb7e4e3f6 0x81f8fffff031ffdf 0xbb03f1ffffe063ff

def z322 : W := mkw 0x87339bcc00000000 0x330e673798000000 0x8ffffffe00000001 0xf31ffffffc000000

def z323 : W := mkw 0x065b2b96d0f76f81 0x100cb6572da1eedf 0x8ffffffff1ffffff 0xff1fffffffe3ffff

def z324 : W := mkw 0xfdff45a1bdbc0004 0x8ffbfe8b437b7800 0xffffe7f1fffe0061 0xffffffcfe3fffc00

def z325 : W := mkw 0xfffffffffdbda316 0xfffffffffffb7b46 0xffffffffffffe3fb 0xffffffffffffffc7

def z326 : W := mkw 0x161bff8652d7fd89 0x502c37ff0ca5affb 0x8e3fff8e31ffffff 0x7d1c7fff1c63ffff

def z327 : W := mkw 0x02010b8600426d81 0x100402170c0084db 0x8e001f8e31c1ff9f 0x5d1c003f1c6383ff

def z328 : W := mkw 0x0008000210d46901 0x000010000421a8d2 0x0000000031c0e008 0x00000000006381c0

def z329 : W := mkw 0xfffffffff0f7ef93 0xfbffffffffe1efdf 0xfffffffff1ffffff 0xffffffffffe3ffff

def z330 : W := mkw 0x8120b05a4001a310 0x23024160b4800346 0x81f8f8fe0001e39b 0xb303f1f1fc0003c7

def z331 : W := mkw 0xda08fe037bd7fd89 0x47b411fc06f7affb 0xfe00ff01ffffffff 0xdffc01fe03ffffff

def z332 : W := mkw 0x161b6fb652d77fa1 0x102c36df6ca5aeff 0x8e3ffffe31ffffff 0x7d1c7ffffc63ffff

def z333 : W := mkw 0x7cd765b0cfaf16a4 0x84f9aecb619f5e2d 0x7fc7e7f1cfff1ff7 0xfeff8fcfe39ffe3f

def z334 : W := mkw 0x21ed01fa943a27b0 0x2843da03f528744f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z335 : W := mkw 0xfffffffdffbf16a6 0xfffffffffbff7e2d 0xffffffffffff1ff7 0xfffffffffffffe3f

def z336 : W := mkw 0x5a004e0000000000 0x40b4009c00000000 0x7e00070000000000 0x40fc000e00000000

def z337 : W := mkw 0xda004e012b405808 0x47b4009c025680b0 0xfe000701ffc01c05 0xcffc000e03ff8038

def z338 : W := mkw 0x8000900000000000 0x0300012000000000 0x8000f80000000001 0x930001f000000000

def z339 : W := mkw 0x32c56fb6c66b7fa1 0x10658adf6d8cd6ff 0x71c7ffffce3fffff 0xfee38fffff9c7fff

def z340 : W := mkw 0xfac4fe01ef69d808 0x47f589fc03ded3b0 0xffc7ff01fffffc7d 0xffff8ffe03fffff8

def z341 : W := mkw 0xcd7ab05bf9b5a314 0xaf9af560b7f36b46 0x8ff8f8fff1f1e3db 0xbb1ff1f1ffe3e3c7

def z342 : W := mkw 0x30c5f5fac62bb7b0 0x20618bebf58c576f 0x71c7ffffce3fffff 0xfee38fffff9c7fff

def z343 : W := mkw 0x30c46430c6291220 0x006188c8618c5224 0x71c0e771ce011c15 0xdee381cee39c0238

def z344 : W := mkw 0xc968b05bf931a310 0x2f92d160b7f26346 0xfff8f8fffff1e3db 0xfffff1f1ffffe3c7

def z345 : W := mkw 0x0001018000020480 0x0000020300000409 0x00070780003f1ff7 0x7c000e0f00007e3f

def z346 : W := mkw 0x0160005880200210 0x2802c000b1004004 0x01c0007000000000 0x00038000e0000000

def z347 : W := mkw 0xc9680001b9300000 0x0f92d00003726000 0xfff80001fff00041 0xeffff00003ffe000

def z348 : W := mkw 0x00402011ef6bdea8 0x0400804023ded7bd 0x00000001fffffffe 0x0c00000003ffffff

def z349 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x0e3f078e01fe1fe6 0x641c7e0f1c03fc3f

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000070000011c15 0x5c00000e00000238

def z351 : W := mkw 0x20c4000084280000 0x0041880001085000 0x71c00001ce000000 0x82e38000039c0000

def z352 : W := mkw 0xd800d40000000000 0x43b001a800000000 0x7000e00000000000 0x82e001c000000000

def z353 : W := mkw 0xffffdfefbdfe6d87 0xffffffbfdf7bfcdb 0xffffffffffffffff 0xffffffffffffffff

def z354 : W := mkw 0xfffffffffb71fb1a 0xfffffffffff6e3f6 0xfffffffffff1ffdf 0xffffffffffffe3ff

def z355 : W := mkw 0x06130b8600c66d81 0x100c26170c018cdb 0x0e071f8e01cfffbe 0x541c0e3f1c039fff

def z356 : W := mkw 0x104165b0c62b16a0 0x002082cb618c562d 0x0000e7f1ce3f1ff6 0x1c0001cfe39c7e3f

def z357 : W := mkw 0xda00de012b40d808 0x47b401bc025681b0 0xfe001f003fc0fc0c 0x45fc003e007f81f8

def z358 : W := mkw 0x061b0b8610102100 0x100c36170c202042 0x8e3f1f8e3031e3db 0x791c7e3f1c6063c7

def z359 : W := mkw 0x20cc0001bdbc0004 0x0c419800037b7800 0x71c70001fffe0061 0xeee38e0003fffc00

def z360 : W := mkw 0x8120904800000000 0x2302412090000000 0x8038180e00000000 0x010070301c000000

def z361 : W := mkw 0xedfeb059fdbd8214 0xafdbfd60b3fb7b04 0xffffe071fffe0061 0xefffffc0e3fffc00

def z362 : W := mkw 0x0128004a10102110 0x2802500094202042 0x0038000e00000000 0x000070001c000000

def z363 : W := mkw 0x00402010c62b16a0 0x00008040218c562d 0x01c0e0f1ce3f1ff7 0xbe0381c1e39c7e3f

def z364 : W := mkw 0xedfeb05bf031a310 0xabdbfd60b7e06346 0xfffff8fff031e3db 0xfbfffff1ffe063c7

def z365 : W := mkw 0xedff01edbdbc0006 0xbfdbfe03db7b7800 0xffff00fffffe0061 0xeffffe01fffffc00

def z366 : W := mkw 0x0413018400000000 0x1008260308000000 0x003f008e00000000 0x20007e011c000000

def z367 : W := mkw 0xf9ecf47bf031a312 0xebf3d9e8f7e06346 0xf1f8f8fff031e3db 0xbbe3f1f1ffe063c7

def z368 : W := mkw 0x02010b8600426d81 0x100402170c0084db 0x00071f8e003fffff 0x7c000e3f1c007fff

def z369 : W := mkw 0xa5b791ec00000002 0xb34b6f23d8000000 0x81fff8fe00000001 0xb303fff1fc000000

def z370 : W := mkw 0xce1a9a0739d4e909 0x579c35340e73a9d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z371 : W := mkw 0xcb68ba5bf971eb18 0x6f96d174b7f2e3d6 0x8ff8f8fff1f1e3db 0xbb1ff1f1ffe3e3c7

def z372 : W := mkw 0x32c56fb0c66b5ea0 0x00658adf618cd6bd 0xffc7fff1ffffffff 0xffff8fffe3ffffff

def z373 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x01c0e071f031e3da 0x8a0381c0e3e063c7

def z374 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x01c0e0f1f031e3db 0xba0381c1e3e063c7

def z375 : W := mkw 0x12006e0042415800 0x002400dc008482b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e00000031c00001 0x4d1c000000638000

def z377 : W := mkw 0x02000a0000000000 0x0004001400000000 0x8e001f0000000001 0x511c003e00000000

def z378 : W := mkw 0xca009a012940c808 0x4794013402528190 0xfe001801ffc0e009 0xcffc003003ff81c0

def z379 : W := mkw 0x3285dfec00000002 0x70650bbfd8000000 0x71c7fffe00000001 0xf2e38ffffc000000

def z380 : W := mkw 0xca00ba016b41d808 0x4794017402d683b0 0x8e001801ffc1fc1c 0x0d1c003003ff83f8

def z381 : W := mkw 0xefb70b8400000000 0x93df6e1708000000 0xffff1f8e00000001 0xf3fffe3f1c000000

def z382 : W := mkw 0x041a000210942100 0x0008340004212842 0x8e3f188e31ffe3fb 0x7d1c7e311c63ffc7

def z383 : W := mkw 0x00480001b0300000 0x0800900003606000 0x00000001f0300040 0x0800000003e06000

def z384 : W := mkw 0xffff4fa5bdbc0006 0xdffffe9f4b7b7800 0xffff0701fffe0061 0xeffffe0e03fffc00

def z385 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8e381f8e31c1ff9e 0x111c703f1c6383ff

def z386 : W := mkw 0xedfeb001fdbd8004 0x8fdbfd6003fb7b00 0xfffff801ffffe079 0xfffffff003ffffc0

def z387 : W := mkw 0x27bf0bee10d66d83 0xb04f7e17dc21acdb 0x8fff1ffe31ffffff 0x7d1ffe3ffc63ffff

def z388 : W := mkw 0xffffff87fffffd8d 0xdfffffff0ffffffb 0xffffff8fffffffff 0xffffffff1fffffff

def z389 : W := mkw 0x041b018010960480 0x0008360300212c09 0x8e3f078031ff1ff7 0x7d1c7e0f0063fe3f

def z390 : W := mkw 0xffb7dfec00020482 0xf3ff6fbfd8000409 0xfffffffe003f1ff7 0xfffffffffc007e3f

def z391 : W := mkw 0xd968f45bfb31b318 0x6fb2d1e8b7f66366 0xf1f8f8fffe31e3db 0xbbe3f1f1fffc63c7

def z392 : W := mkw 0xf8c4f431ef299228 0x47f189e863de5324 0x71c0e071ce000000 0x82e381c0e39c0000

def z393 : W := mkw 0x5a00fe004b41d808 0x44b401fc009683b0 0x7e00ff000fc1fc1c 0x54fc01fe001f83f8

def z394 : W := mkw 0x30c565b0c0210200 0x00618acb61804204 0x71c7e7f1c03103d3 0xfae38fcfe3806207

def z395 : W := mkw 0x8000b00160018000 0x0300016002c00300 0x0000e001c0000000 0x820001c003800000

def z396 : W := mkw 0x25f701fc842a06a2 0xb04bee03f908540d 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z397 : W := mkw 0x0001018000020480 0x0000020300000409 0x00070700000e1c24 0x44000e0e00001c38

def z398 : W := mkw 0x877aba5ff0f5eb11 0x3b0ef574bfe1ebd6 0x8ff8f8fff1f1e3db 0xbb1ff1f1ffe3e3c7

def z399 : W := mkw 0x7a854fa00f4a5ca8 0x44f50a9f401e94b9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z400 : W := mkw 0x27ff0b8694fe6d85 0x984ffe170d29fcdb 0x8fff1f8e31ffffff 0x7d1ffe3f1c63ffff

def z401 : W := mkw 0x1200fe016b41d808 0x442401fc02d683b0 0x0000ff01ffc1fc1c 0x1c0001fe03ff83f8

def z402 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000080003103d3 0x3800000100006207

def z403 : W := mkw 0x0412000000840000 0x0008240000010800 0x0e07000001ce0020 0x441c0e0000039c00

def z404 : W := mkw 0x0000201040010200 0x0000004020800204 0x0000e0f000010392 0x100001c1e0000207

def z405 : W := mkw 0x1000640042011000 0x002000c800840220 0x7000e001ce000000 0x82e001c0039c0000

def z406 : W := mkw 0xfdb745a000000000 0x83fb6e8b40000000 0xffffe7f000000001 0xf3ffffcfe0000000

def z407 : W := mkw 0x35f765fcc62b16a2 0xb06beecbf98c562d 0x71ffe7ffce3f1ff7 0xfee3ffcfff9c7e3f

def z408 : W := mkw 0x8368ba5bf071eb10 0x2b06d174b7e0e3d6 0x8ff8fffff1f1ffdf 0xff1ff1ffffe3e3ff

def z409 : W := mkw 0xda00fe5b6b41fb18 0x67b401fcb6d683f6 0xfe00ffffffc1ff9f 0xdffc01ffffff83ff

def z410 : W := mkw 0x8369bbdff073ef91 0x3b06d377bfe0e7df 0x81f8fffff031ffdf 0xbb03f1ffffe063ff

def z411 : W := mkw 0x5a006e004b415808 0x44b400dc009682b0 0x7e00e701cfc11c15 0xdefc01ce039f8238

def z412 : W := mkw 0xcf3b0b8739d66d85 0x9f9e76170e73acdb 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z413 : W := mkw 0x0008000210102100 0x0000100004202042 0x8038180e3000e008 0x010070301c6001c0

def z414 : W := mkw 0x7ac56fb0cf6b5ea8 0x44f58adf619ed6bd 0x7fc7e7f1cfff1ff7 0xfeff8fcfe39ffe3f

def z415 : W := mkw 0xcf3b9bce10d66d83 0xf39e77379c21acdb 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z416 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x0e07070031fffffe 0x4c1c0e0e0063ffff

def z417 : W := mkw 0x0008000210d66d81 0x000010000421acdb 0x8038188e31ffffff 0x3d0070311c63ffff

def z418 : W := mkw 0xefff0b85bdfe4c85 0x9fdffe170b7bfc99 0xffff0701fffe1c65 0xeffffe0e03fffc38

def z419 : W := mkw 0xde13ff856b41d808 0x57bc27ff0ad683b0 0xfe3fff8fffc1fc1d 0xfffc7fff1fff83f8

def z420 : W := mkw 0xefb79bec00000002 0xf3df6f37d8000000 0x8fff18fe00000000 0x211ffe31fc000000

def z421 : W := mkw 0x308545a0060a14a0 0x00610a8b400c1429 0x71c7e7f00e0e1c25 0xf6e38fcfe01c1c38

def z422 : W := mkw 0x8168b001f0318000 0x0b02d16003e06300 0x81f8f801f031e059 0xbb03f1f003e063c0

def z423 : W := mkw 0x06130b8400404800 0x100c261708008090 0x8e3f1f8e31c1fc1d 0x7d1c7e3f1c6383f8

def z424 : W := mkw 0xc920904800000002 0xe392412090000000 0x0000000000000000 0x0000000000000000

def z425 : W := mkw 0x30cd65b2d6ff7fa1 0x00619acb65adfeff 0x71c7e7f1ffffffff 0xfee38fcfe3ffffff

def z426 : W := mkw 0x9168f45bf231b310 0x2b22d1e8b7e46366 0xf1f8fffffe31ffdf 0xffe3f1fffffc63ff

def z427 : W := mkw 0x1201fffc420316a2 0x702403fff884062d 0x0000fffe00011f96 0x100001fffc00023f

def z428 : W := mkw 0x81680001bdbc0004 0x0f02d000037b7800 0x81f80001fffe0061 0xaf03f00003fffc00

def z429 : W := mkw 0x6c96000000000000 0x80d92c0000000000 0x7e07000000000000 0x40fc0e0000000000

def z430 : W := mkw 0x873b9bce10d66d81 0x330e77379c21acdb 0x8ffffffe31ffffff 0xff1ffffffc63ffff

def z431 : W := mkw 0xda01dfec00000002 0x73b403bfd8000000 0xfe00fffe00000001 0xd3fc01fffc000000

def z432 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c0e7f1ce011f96 0x92e381cfe39c023f

def z433 : W := mkw 0x1200de0000000000 0x402401bc00000000 0x0000ff0000000000 0x100001fe00000000

def z434 : W := mkw 0x8168905a90302310 0x2b02d120b5206046 0x81f8f8fe003003c3 0xb303f1f1fc006007

def z435 : W := mkw 0xda00fe0160018000 0x43b401fc02c00300 0xfe00ff01f001e019 0xdbfc01fe03e003c0

def z436 : W := mkw 0x06130b8600426d81 0x100c26170c0084db 0x8e3f1f8e0001ff9f 0x711c7e3f1c0003ff

def z437 : W := mkw 0x30c565b1ef6bdea8 0x04618acb63ded7bd 0x71c7e7f1ffffffff 0xfee38fcfe3ffffff

def z438 : W := mkw 0x0001018000020480 0x0000020300000409 0x00070080003e03e2 0x20000e0100007c07

def z439 : W := mkw 0x100145a0020214a0 0x0020028b40040429 0x0000070000001c04 0x0000000e00000038

def z440 : W := mkw 0x000000012940c808 0x0400000002528190 0x0000000031c0e008 0x00000000006381c0

def z441 : W := mkw 0xf9e4f401ef29900c 0xcff3c9e803de5320 0x71c0e001ce000000 0x82e381c0039c0000

def z442 : W := mkw 0x0201bbde4043ef91 0x30040377bc8087df 0x0000fffe0001ff9e 0x100001fffc0003ff

def z443 : W := mkw 0x061b0b8410940000 0x100c361708212800 0x8e3f1f8e31fe0061 0x7d1c7e3f1c63fc00

def z444 : W := mkw 0x308565b0420316a0 0x00610acb6084062d 0x71c7e7f000011f97 0xf2e38fcfe000023f

def z445 : W := mkw 0xc80020016b41d808 0x0790004002d683b0 0xfe000001ffc1fc1d 0xcffc000003ff83f8

def z446 : W := mkw 0xda48fe13fb71fb18 0x4fb491fc27f6e3f6 0xfe00ff01fff1ffdf 0xdffc01fe03ffe3ff

def z447 : W := mkw 0xeffe0a07bdfc6905 0x9fdffc140f7bf8d2 0xffff180ffffee069 0xeffffe301ffffdc0

def z448 : W := mkw 0xfdfe6431ffbd1224 0x8ffbfcc863ff7a24 0xffffe071fffe0061 0xefffffc0e3fffc00

def z449 : W := mkw 0x0008000210102100 0x0000100004202042 0x000000003031e3da 0x08000000006063c7

def z450 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfe3f1f0e00000000 0x41fc7e3e1c000000

def z451 : W := mkw 0x861bbb8770d7ed81 0x130c37770ee1afdb 0x8e3fff8ff1ffffff 0xff1c7fff1fe3ffff

def z452 : W := mkw 0x00482001fffdd80c 0x0c00904003fffbb0 0x00000001fffffc7c 0x0c00000003fffff8

def z453 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0x7fc7e77000000000 0xc2ff8fcee0000000

def z454 : W := mkw 0x308565a042011000 0x00610acb40840220 0x71c7e7f1ce011c15 0xfee38fcfe39c0238

def z455 : W := mkw 0x00400001ad280004 0x0c008000035a5000 0x00000001ce000000 0x00000000039c0000

def z456 : W := mkw 0xda00de000b405808 0x47b401bc001680b0 0xfe00ff000fc01c05 0xd7fc01fe001f8038

def z457 : W := mkw 0xe8c40001ad280000 0x07d18800035a5000 0xffc70001fffe0061 0xefff8e0003fffc00

def z458 : W := mkw 0xf9e4f479e0218212 0xebf3c9e8f3c04304 0x71c0e071c0000000 0x82e381c0e3800000

def z459 : W := mkw 0x061b0b8610962581 0x100c36170c212c4b 0x8e3f1f8e003e03e3 0x711c7e3f1c007c07

def z460 : W := mkw 0xda48fe01fffdd80c 0x4fb491fc03fffbb0 0xfe00ff01fffffc7d 0xdffc01fe03fffff8

def z461 : W := mkw 0x8008b0037011a100 0x0300116006e02342 0x8038f88ff031e3db 0xbb0071f11fe063c7

def z462 : W := mkw 0x308545a000020480 0x00610a8b40000409 0x71c7e7f0003f1ff7 0xfee38fcfe0007e3f

def z463 : W := mkw 0x045a0001bdbc0004 0x0c08b400037b7800 0x8e3f0001fffe0061 0x6d1c7e0003fffc00

def z464 : W := mkw 0xb1a5d5e800000000 0x23634babd0000000 0xf1fffffe00000001 0xf3e3fffffc000000

def z465 : W := mkw 0x0000904a0000a110 0x2000012094000142 0x0000180e0000e008 0x000000301c0001c0

def z466 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0x8fff000031fe0060 0x211ffe000063fc00

def z467 : W := mkw 0xf9e4f478c6291222 0xe3f3c9e8f18c5224 0x71c0e071ce000000 0x82e381c0e39c0000

def z468 : W := mkw 0xf8c565b1ef2b16a0 0x07f18acb63de562d 0xffc7e7f1ffff1ff7 0xffff8fcfe3fffe3f

def z469 : W := mkw 0x0008b05a5011a310 0x20001160b4a02346 0x8038f8fe3031e3db 0x390071f1fc6063c7

def z470 : W := mkw 0x877bbbdff031a310 0x3b0ef777bfe06346 0x8ffffffff031e3db 0xfb1fffffffe063c7

def z471 : W := mkw 0xdf32de4c00000002 0xf3be65bc98000000 0xfe38ff0e00000001 0xd3fc71fe1c000000

def z472 : W := mkw 0x000020004241d808 0x00000040008483b0 0x000000000001fc1c 0x00000000000003f8

def z473 : W := mkw 0xfac5ffb0c62b16a0 0x43f58bff618c562d 0xffc7fff1ce3f1ff7 0xffff8fffe39c7e3f

def z474 : W := mkw 0x0532004c00000002 0xb00a640098000000 0x0038000e00000000 0x000070001c000000

def z475 : W := mkw 0xedfe2001fffdd80c 0x8fdbfc4003fffbb0 0xffff0001fffffc7d 0xeffffe0003fffff8

def z476 : W := mkw 0x8128b04b7011a110 0x2b02516096e02342 0x8038f80ff001e019 0x9b0071f01fe003c0

def z477 : W := mkw 0xffbfdfee10962583 0xf3ff7fbfdc212c4b 0xfffffffe003e03e3 0xf3fffffffc007c07

def z478 : W := mkw 0x041a000610942101 0x100834000c212842 0x0038000e00000000 0x000070001c000000

def z479 : W := mkw 0xefbf0b8610d66d81 0x93df7e170c21acdb 0xffff1f8e31ffffff 0xfffffe3f1c63ffff

def z480 : W := mkw 0xeffe9a01bdfcc80c 0xcfdffd34037bf990 0xffff1801fffee069 0xeffffe3003fffdc0

def z481 : W := mkw 0xedb600000d8c0004 0x87db6c00001b1800 0xffff00000fce0021 0xe7fffe00001f9c00

def z482 : W := mkw 0x25fe005a94bc2314 0xa84bfc00b5297846 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z483 : W := mkw 0x0000b05840018210 0x20000160b0800304 0x0000e07000000000 0x000001c0e0000000

def z484 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c7e771ce0e1c24 0xc6e38fcee39c1c38

def z485 : W := mkw 0xeffe0a01bdfc4804 0x8fdffc14037bf890 0xffff1f01fffffc7d 0xfffffe3e03fffff8

def z486 : W := mkw 0xe9e4b059ed298214 0xafd3c960b3da5304 0x71c0e071ce000000 0x82e381c0e39c0000

def z487 : W := mkw 0x1201ffec4241d80a 0x702403ffd88483b0 0x0000fffe0001fc1c 0x100001fffc0003f8

def z488 : W := mkw 0x02010b8000424c80 0x0004021700008499 0x8e071f8031ffffff 0x7d1c0e3f0063ffff

def z489 : W := mkw 0x26df0b8694fe6d81 0x104dbe170d29fcdb 0xffff1f8fffffffff 0xfffffe3f1fffffff

def z490 : W := mkw 0x8120904920008010 0x2b02412092400100 0x0000000000000000 0x0000000000000000

def z491 : W := mkw 0xffb7ffec42011002 0xf3ff6fffd8840220 0xffffffffce011c15 0xffffffffff9c0238

def z492 : W := mkw 0xfac4fe31ef69da28 0x47f589fc63ded3b4 0xffc0ff71ffc1fc1d 0xdfff81fee3ff83f8

def z493 : W := mkw 0x7ed76fb4c62b16a2 0xd0fdaedf698c562d 0x7fc7e7f1ce3f1ff7 0xfeff8fcfe39c7e3f

def z494 : W := mkw 0xfdfef401ffbd900c 0xcffbfde803ff7b20 0xffffe001fffe0061 0xefffffc003fffc00

def z495 : W := mkw 0x1000d46800000002 0x602001a8d0000000 0x0000e07000000000 0x000001c0e0000000

def z496 : W := mkw 0xffbfdfef3010a112 0xfbff7fbfde602142 0xfffffffe3000e009 0xf3fffffffc6001c0

def z497 : W := mkw 0x8048b013f031a310 0x0b00916027e06346 0x8000f801f031e3db 0x9b0001f003e063c7

def z498 : W := mkw 0x00480003bdfe6d85 0x0c009000077bfcdb 0x00000001fffffffe 0x0c00000003ffffff

def z499 : W := mkw 0x25ff01fe90302312 0xb84bfe03fd206046 0x01ff00fe003003c2 0x2003fe01fc006007

def z500 : W := mkw 0x0000000000404800 0x0000000000008090 0x0000000031c1fc1c 0x0c000000006383f8

def z501 : W := mkw 0x4c12000009840004 0x8498240000130800 0x0e00000001c00000 0x001c000000038000

def z502 : W := mkw 0x2084000004080000 0x0041080000081000 0x700700000e0e0020 0x44e00e00001c1c00

def z503 : W := mkw 0xfdfe6401ffbd1004 0x8ffbfcc803ff7a20 0xffffe701ffff1c75 0xffffffce03fffe38

def z504 : W := mkw 0x12014fa400000002 0x5024029f48000000 0x0000070000000000 0x0000000e00000000

def z505 : W := mkw 0x1200fe004241d808 0x402401fc008483b0 0x7000ff01ce01fc1d 0xdee001fe039c03f8

def z506 : W := mkw 0x8128904b3010a110 0x2b02512096602142 0x81f8f8fe3000e009 0xb303f1f1fc6001c0

def z507 : W := mkw 0x30c46430c62b16a0 0x006188c8618c562d 0x71c0e071ce3f1ff6 0x8ee381c0e39c7e3f

def z508 : W := mkw 0x0000200040010000 0x0000004000800200 0x0000e001c0010011 0x9a0001c003800200

def z509 : W := mkw 0xcd3a904b3994a114 0xaf9a752096732942 0x8e38180e31c0e008 0x011c70301c6381c0

def z510 : W := mkw 0xedfe000094bc0004 0x8bdbfc0001297800 0xffff0000003e0061 0xe3fffe0000007c00

def z511 : W := mkw 0xf9e4d469ad280006 0xeff3c9a8d35a5000 0x71c0e071ce000000 0x82e381c0e39c0000

def z512 : W := mkw 0x000000000d8c0004 0x04000000001b1800 0x000000000fce0020 0x04000000001f9c00

def z513 : W := mkw 0x7e974fa400c64c83 0xd0fd2e9f48018c99 0x7e07070001ce1c24 0x44fc0e0e00039c38

def z514 : W := mkw 0x00482011ffbf16a4 0x0c00904023ff7e2d 0x00000001ffff1ff6 0x0c00000003fffe3f

def z515 : W := mkw 0xcf7aba5ff031a312 0xfb9ef574bfe06346 0x8ff8f8fff031e3db 0xbb1ff1f1ffe063c7

def z516 : W := mkw 0x000101ec00000002 0x30000203d8000000 0x000000fe00000000 0x00000001fc000000

def z517 : W := mkw 0x7e974fa40d8c0006 0xd4fd2e9f481b1800 0x7e0707000fce0020 0x44fc0e0e001f9c00

def z518 : W := mkw 0xcd3a000139940004 0x8f9a740002732800 0x8e3f000031fe0061 0x6d1c7e000063fc00

def z519 : W := mkw 0x5e134f840bc65c89 0x54bc269f08178cb9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z520 : W := mkw 0x27b70bec00000002 0xb04f6e17d8000000 0x8fff1ffe00000001 0x711ffe3ffc000000

def z521 : W := mkw 0x0000000200426d81 0x00000000040084db 0x000000000001ff9e 0x00000000000003ff

def z522 : W := mkw 0xedbe00013d9c0004 0x8fdb7c00027b3800 0xfe3f00003fce0020 0x45fc7e00007f9c00

def z523 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x8038180ff031e3da 0x090070301fe063c7

def z524 : W := mkw 0x12004e0002405808 0x4024009c000480b0 0x0000070000001c04 0x0000000e00000038

def z525 : W := mkw 0xcf3a9a4f3010a112 0xfb9e75349e602142 0x8e38180e3000e008 0x011c70301c6001c0

def z526 : W := mkw 0x061a0a0610d46901 0x100c34140c21a8d2 0x8e381f0e31c1fc1d 0x5d1c703e1c6383f8

def z527 : W := mkw 0x35ff65b0d6bf16a4 0x886bfecb61ad7e2d 0x71ffe7f1ce3f1ff7 0xfee3ffcfe39c7e3f

def z528 : W := mkw 0x308545a0060a14a0 0x00610a8b400c1429 0x700707800e3f1ff7 0x7ce00e0f001c7e3f

def z529 : W := mkw 0x7e97dfec00000002 0xf0fd2fbfd8000000 0x7e07fffe00000000 0x50fc0ffffc000000

def z530 : W := mkw 0xf9a5d5e800000002 0xe3f34babd0000000 0x71c7e7f000000001 0xf2e38fcfe0000000

def z531 : W := mkw 0x857a0001b0b40000 0x0b0af40003616800 0x8fff0001f1fe0061 0xef1ffe0003e3fc00

def z532 : W := mkw 0x0008000010940000 0x0000100000212800 0x0000000031fe0060 0x0c0000000063fc00

def z533 : W := mkw 0xdb68fe01fb71d808 0x4fb6d1fc03f6e3b0 0xfff8ff01fff1fc5d 0xfffff1fe03ffe3f8

def z534 : W := mkw 0x36974fa406ce5ca1 0x106d2e9f480d9cb9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z535 : W := mkw 0xb7fffffff6ffffb1 0x3b6fffffffedffff 0xffffffffffffffff 0xffffffffffffffff

def z536 : W := mkw 0x161b6f8652d77d81 0x102c36df0ca5aefb 0xfe3fff8fffffffff 0xfffc7fff1fffffff

def z537 : W := mkw 0x0000000000000000 0x0000000000000000 0x70000001ce000001 0xcee00000039c0000

def z538 : W := mkw 0x065b0b87bdfe6d85 0x1c0cb6170f7bfcdb 0x8e3f1f8fffffffff 0x7d1c7e3f1fffffff

def z539 : W := mkw 0x100165b0420316a0 0x002002cb6084062d 0x0007e7f0003f1ff7 0x7c000fcfe0007e3f

def z540 : W := mkw 0xe9ec0001bdbc0004 0x8fd3d800037b7800 0x71c00001fffe0060 0x8ee3800003fffc00

def z541 : W := mkw 0x2084000000000000 0x0041080000000000 0x71c7000000000001 0xe2e38e0000000000

def z542 : W := mkw 0x00002010420316a0 0x000000402084062d 0x0000000000011f96 0x000000000000023f

def z543 : W := mkw 0xfffede01bdbc0004 0xcffffdbc037b7800 0xffffff01fffe0061 0xfffffffe03fffc00

def z544 : W := mkw 0xffbfdfee10d46903 0xf3ff7fbfdc21a8d2 0xfffffffe31c0e009 0xf3fffffffc6381c0

def z545 : W := mkw 0x36d76fb4c62b16a0 0x106daedf698c562d 0xffffffffce3f1ff7 0xffffffffff9c7e3f

def z546 : W := mkw 0xd800f4016b41d808 0x47b001e802d683b0 0x7000e001ffc1fc1c 0x8ee001c003ff83f8

def z547 : W := mkw 0xb1e4f479e6299230 0x2b63c9e8f3cc5324 0x71c0e071ce000000 0x82e381c0e39c0000

def z548 : W := mkw 0x0000b00040018000 0x0000016000800300 0x0000f8000001e018 0x100001f0000003c0

def z549 : W := mkw 0xcb289a4b3950e918 0x6f9651349672a1d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z550 : W := mkw 0xcf329a4d2940c80a 0xf79e65349a528190 0x8e38180e31c0e008 0x011c70301c6381c0

def z551 : W := mkw 0xc8480001bdbc0004 0x0f909000037b7800 0xfe000001fffe0061 0xcffc000003fffc00

def z552 : W := mkw 0x0008000210962581 0x0000100004212c4b 0x00000000003e03e2 0x0000000000007c07

def z553 : W := mkw 0x6e970b840dce4c85 0x94dd2e17081b9c99 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z554 : W := mkw 0xfbe4fe01ef69d80c 0xcff7c9fc03ded3b0 0xffc0ff01ffc1fc1d 0xdfff81fe03ff83f8

def z555 : W := mkw 0x25fe0001bdbc0004 0x8c4bfc00037b7800 0x01ff0001fffe0060 0x2c03fe0003fffc00

def z556 : W := mkw 0x06130b8400000000 0x100c261708000000 0x0e07070000000000 0x401c0e0e00000000

def z557 : W := mkw 0x25ff01b094be06a4 0x884bfe0361297c0d 0x01ff00f0003e03e2 0x2003fe01e0007c07

def z558 : W := mkw 0x36d76fb4c6ef5ea1 0x106daedf698ddebd 0x7fc7e7f1cfff1ff7 0xfeff8fcfe39ffe3f

def z559 : W := mkw 0x06130b8400c64c81 0x100c261708018c99 0x0e07078001ff1ff7 0x7c1c0e0f0003fe3f

def z560 : W := mkw 0xde1bdf8610d66d81 0x53bc37bf0c21acdb 0xfe3fff8e31ffffff 0xfffc7fff1c63ffff

def z561 : W := mkw 0x000020016b019008 0x0400004002d60320 0x00000001ce000000 0x00000000039c0000

def z562 : W := mkw 0xeffe9a4dbdbc0006 0xffdffd349b7b7800 0xffff180ffffe0061 0xeffffe301ffffc00

def z563 : W := mkw 0x00402010c0210200 0x0000804021804204 0x00000001c03103d2 0x0800000003806207

def z564 : W := mkw 0xedbe000139940004 0x8fdb7c0002732800 0xffff000031c00001 0xe3fffe0000638000

def z565 : W := mkw 0x8128000130100000 0x0b02500002602000 0x8038000030000000 0x0100700000600000

def z566 : W := mkw 0x0000200160018000 0x0000004002c00300 0x00000001f001e018 0x0800000003e003c0

def z567 : W := mkw 0x873a9a4f30d4e911 0x3b0e75349e61a9d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z568 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8e3f1f0e31cefc2c 0x451c7e3e1c639df8

def z569 : W := mkw 0x8168905bb030a310 0x2b02d120b7606146 0x81f818fe3030e3ca 0x2103f031fc6061c7

def z570 : W := mkw 0x02090b8610526d81 0x100412170c20a4db 0x80381f8e3031ffdf 0x3900703f1c6063ff

def z571 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xfff80001ffc00000 0x83fff00003ff8000

def z572 : W := mkw 0x00412190c0230680 0x000082432180460d 0x01c7e7f1c03f1ff7 0xfe038fcfe3807e3f

def z573 : W := mkw 0xce1b9b8739d6ed89 0x579c37370e73addb 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z574 : W := mkw 0x065b2b96d6ff7fa1 0x100cb6572dadfeff 0x8e3f1f8fffffffff 0x7d1c7e3f1fffffff

def z575 : W := mkw 0x061a0a0610d46901 0x100c34140c21a8d2 0x8e38188e31f1e3db 0x391c70311c63e3c7

def z576 : W := mkw 0xc800900129008008 0x4790012002520100 0x0000000000000000 0x0000000000000000

def z577 : W := mkw 0x02000a0600406901 0x100400140c0080d2 0x0000180e0000e008 0x000000301c0001c0

def z578 : W := mkw 0x25bf01ee10962583 0xb04b7e03dc212c4b 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z579 : W := mkw 0x0000000000000000 0x0000000000000000 0x00070000003e0061 0x6c000e0000007c00

def z580 : W := mkw 0x7e974fa400000002 0xd0fd2e9f48000000 0x7fc7e7f000000001 0xf2ff8fcfe0000000

def z581 : W := mkw 0xcd32000000000000 0x839a640000000000 0x8e38000000000000 0x011c700000000000

def z582 : W := mkw 0x000000000b405808 0x04000000001680b0 0x000000000fc01c04 0x04000000001f8038

def z583 : W := mkw 0x308565b0460b16a0 0x00610acb608c162d 0x7007e7f00e0f1fb6 0x54e00fcfe01c1e3f

def z584 : W := mkw 0x02010b8400424c81 0x1004021708008499 0x0000070000001c04 0x0000000e00000038

def z585 : W := mkw 0xfff7dfedad280006 0xffffefbfdb5a5000 0xffffffffce000001 0xf3ffffffff9c0000

def z586 : W := mkw 0xfa85ffa16f4bdca8 0x47f50bff42de97b9 0xfe07ff01ffcffc3d 0xdffc0ffe03ff9ff8

def z587 : W := mkw 0x8168005bb0302310 0x2b02d000b7606046 0x81f800fff03003c3 0xab03f001ffe06007

def z588 : W := mkw 0xe9ec0001bd380004 0x8fd3d800037a7000 0xf1f80001fe300041 0xabe3f00003fc6000

def z589 : W := mkw 0x34df65b6d6bf37a1 0x1069becb6dad7e6f 0x71ffe7ffce3f1ff7 0xfee3ffcfff9c7e3f

def z590 : W := mkw 0xa1ec0001b4380000 0x0b43d80003687000 0xf1ff0001fe3e0061 0xefe3fe0003fc7c00

def z591 : W := mkw 0xfdfff5fbffbfb7b4 0xaffbffebf7ff7f6f 0xffffffffffffffff 0xffffffffffffffff

def z592 : W := mkw 0x877b0b87b0f66d81 0x1b0ef6170f61ecdb 0x8fff1f8ff1ffffff 0xff1ffe3f1fe3ffff

def z593 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x003f1f8e003ffffe 0x30007e3f1c007fff

def z594 : W := mkw 0xffb6de0000000000 0xc3ff6dbc00000000 0xffffff0000000001 0xf3fffffe00000000

def z595 : W := mkw 0x041b018610d66d81 0x100836030c21acdb 0x003f008e31fffffe 0x2c007e011c63ffff

def z596 : W := mkw 0x5e1b4f861bd67d89 0x54bc369f0c37acfb 0xfe3f1f8e3fffffff 0x7dfc7e3f1c7fffff

def z597 : W := mkw 0xffb7ffec4241d80a 0xf3ff6fffd88483b0 0xfffffffe0001fc1d 0xf3fffffffc0003f8

def z598 : W := mkw 0xfdf765b0c62b16a0 0x83fbeecb618c562d 0xffffe7f1ce3f1ff7 0xffffffcfe39c7e3f

def z599 : W := mkw 0x8168b05bf0f7ef91 0x2b02d160b7e1efdf 0x81f8f8fff1ffffff 0xbf03f1f1ffe3ffff

def z600 : W := mkw 0x4800000009000000 0x0490000000120000 0x7e0000000fc00000 0x44fc0000001f8000

def z601 : W := mkw 0x041a000010940000 0x0008340000212800 0x8e38000031c00000 0x011c700000638000

def z602 : W := mkw 0xffbfdfee10102102 0xf3ff7fbfdc202042 0xfffffffe3031e3db 0xfbfffffffc6063c7

def z603 : W := mkw 0xedff01b1bdbe06a4 0x8fdbfe03637b7c0d 0xffff00f1fffe03e3 0xeffffe01e3fffc07

def z604 : W := mkw 0x0000000129000000 0x0400000002520000 0x00000001ffc00000 0x0c00000003ff8000

def z605 : W := mkw 0x02080a0210d66d81 0x000410140421acdb 0x8e001f0031ffffff 0x5d1c003e0063ffff

def z606 : W := mkw 0x9369fffff031a312 0x7b26d3ffffe06346 0x81f8fffff031e3db 0xbb03f1ffffe063c7

def z607 : W := mkw 0xdf7bffdffbf7ff99 0x7fbef7ffbff7efff 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0x369f4fa616de7da1 0x106d3e9f4c2dbcfb 0xfe3f1f8e3fffffff 0x7dfc7e3f1c7fffff

def z609 : W := mkw 0xb1edf5fbf031a310 0x2b63dbebf7e06346 0xf1fffffff031e3db 0xfbe3ffffffe063c7

def z610 : W := mkw 0xb1ed65b1f63b16a0 0x0b63dacb63ec762d 0xf1ffe7f1fe3f1ff7 0xffe3ffcfe3fc7e3f

def z611 : W := mkw 0x30c545a0862a14a0 0x00618a8b410c5429 0x71c70701ce3e1c65 0xeee38e0e039c7c38

def z612 : W := mkw 0x000820037bd7fd89 0x0400104006f7affb 0x00000001fffffffe 0x0c00000003ffffff

def z613 : W := mkw 0xe9a4000000000000 0x83d3480000000000 0x71c0000000000000 0x82e3800000000000

def z614 : W := mkw 0x02002a016b41d808 0x0404005402d683b0 0x8e001f01ffc1fc1d 0x5d1c003e03ff83f8

def z615 : W := mkw 0xffb6fe016b41d808 0xc7ff6dfc02d683b0 0xffffff01ffc1fc1d 0xfffffffe03ff83f8

def z616 : W := mkw 0x0000000000c64c81 0x0000000000018c99 0x0000000001ce1c24 0x0400000000039c38

def z617 : W := mkw 0xffffffb1ffffdeac 0xcfffffff63ffffbd 0xfffffff1ffffffff 0xffffffffe3ffffff

def z618 : W := mkw 0x20c501b0842a06a0 0x00418a036108540d 0x71c700f1ce3e03e3 0xeee38e01e39c7c07

def z619 : W := mkw 0x0008000010100000 0x0000100000202000 0x8038000030300041 0x2900700000606000

def z620 : W := mkw 0x0008000139940004 0x0c00100002732800 0x0000000031c00000 0x0000000000638000

def z621 : W := mkw 0xffb7fffe4001a312 0xf3ff6ffffc800346 0xfffffffe0001e39b 0xf3fffffffc0003c7

def z622 : W := mkw 0xfe96fe016fcdd80c 0xc7fd2dfc02df9bb0 0xfe07ff01ffcffc3d 0xdffc0ffe03ff9ff8

def z623 : W := mkw 0x8160b059e0218210 0x2b02c160b3c04304 0x81f8f8ffc0000001 0xb303f1f1ff800000

def z624 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8e3f188e31fee3ea 0x211c7e311c63fdc7

def z625 : W := mkw 0x7e9f4fa610d66d83 0xd0fd3e9f4c21acdb 0xfe3f1f8e31ffffff 0x7dfc7e3f1c63ffff

def z626 : W := mkw 0x0000000000000000 0x0000000000000000 0x800018003001e019 0x19000030006003c0

def z627 : W := mkw 0xfdb7d5ec00000002 0xf3fb6fabd8000000 0x71ffe0fe00000000 0xa2e3ffc1fc000000

def z628 : W := mkw 0x308545a000000000 0x00610a8b40000000 0x7007070000000000 0x40e00e0e00000000

def z629 : W := mkw 0x100145a000000000 0x0020028b40000000 0x0000e7f000000000 0x100001cfe0000000

def z630 : W := mkw 0x6e9f0b861dde6d85 0x94dd3e170c3bbcdb 0xfe3f1f8e3fffffff 0x7dfc7e3f1c7fffff

def z631 : W := mkw 0xffb7fffc420316a2 0xf3ff6ffff884062d 0xfffffffe00011f97 0xf3fffffffc00023f

def z632 : W := mkw 0xcf3a9a4d39940006 0xff9e75349a732800 0x8e38180e31c00000 0x011c70301c638000

def z633 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0x71ff0001ce3e0060 0xa2e3fe00039c7c00

def z634 : W := mkw 0xffbfffef7bd7fd8b 0xf7ff7fffdef7affb 0xffffffffffffffff 0xffffffffffffffff

def z635 : W := mkw 0x34df65b0d6bf16a0 0x0069becb61ad7e2d 0xffffe7f1ffff1ff7 0xffffffcfe3fffe3f

def z636 : W := mkw 0x0000200042011000 0x0000004000840220 0x00000001ce011c14 0x0c000000039c0238

def z637 : W := mkw 0xefb69a4c00000002 0xf3df6d3498000000 0xffff180e00000001 0xe3fffe301c000000

def z638 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0x8e00ff0031c1fc1c 0x111c01fe006383f8

def z639 : W := mkw 0xda00de012940c808 0x47b401bc02528190 0xfe00ff0031c0e009 0xd3fc01fe006381c0

def z640 : W := mkw 0x20c521b0c42b06a0 0x00418a436188560d 0x01c7e0f1c03f03f3 0xba038fc1e3807e07

def z641 : W := mkw 0x06130b8400020480 0x100c261708000409 0x8e3f1f8e003f1ff7 0x7d1c7e3f1c007e3f

def z642 : W := mkw 0x8168b05bfb71fb18 0x2f02d160b7f6e3f6 0x81f8f8fffff1ffdf 0xbf03f1f1ffffe3ff

def z643 : W := mkw 0x10406410c62b16a0 0x002080c8218c562d 0x7000e701ce3f1ff7 0xdee001ce039c7e3f

def z644 : W := mkw 0x30cd65b1ffbf16a4 0x0c619acb63ff7e2d 0x71c7e7f1ffff1ff7 0xfee38fcfe3fffe3f

def z645 : W := mkw 0x041a000010940000 0x0008340000212800 0x003f0000003e0060 0x20007e0000007c00

def z646 : W := mkw 0xffb7dfee00426d83 0xf3ff6fbfdc0084db 0xfffffffe0001ff9f 0xf3fffffffc0003ff

def z647 : W := mkw 0xc800000129000000 0x0790000002520000 0x8e00000031c00000 0x011c000000638000

def z648 : W := mkw 0xa5fe0001b4bc0004 0x8b4bfc0003697800 0x81ff0001f03e0061 0xab03fe0003e07c00

def z649 : W := mkw 0x100165b0420316a0 0x002002cb6084062d 0x7000e7f1ce011f97 0xdee001cfe39c023f

def z650 : W := mkw 0x00412190c62b16a0 0x00008243218c562d 0x00070781ce3f1ff7 0x7c000e0f039c7e3f

def z651 : W := mkw 0x0040b05ac021a310 0x20008160b5804346 0x01c0f8ffc031e3db 0xba0381f1ff8063c7

def z652 : W := mkw 0x161bdfee10d66d83 0x702c37bfdc21acdb 0x8e3ffffe31ffffff 0x7d1c7ffffc63ffff

def z653 : W := mkw 0xde1afe077bd5f909 0x57bc35fc0ef7abf2 0xfe38ff0fffc1fc1d 0xdffc71fe1fff83f8

def z654 : W := mkw 0xda00de0129000000 0x47b401bc02520000 0xfe00ff01ffc00001 0xdffc01fe03ff8000

def z655 : W := mkw 0xffb74fa400000002 0xd3ff6e9f48000000 0xffff070000000001 0xe3fffe0e00000000

def z656 : W := mkw 0x37b7dfec00000002 0xf06f6fbfd8000000 0x01fffffe00000000 0x3003fffffc000000

def z657 : W := mkw 0xf9e565b1ef2b16a4 0x8ff3cacb63de562d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z658 : W := mkw 0x6dfe00009dbc0004 0x8cdbfc00013b7800 0x7fff00000ffe0060 0x64fffe00001ffc00

def z659 : W := mkw 0xd800f4016b019008 0x47b001e802d60320 0x7000e701ce011c15 0xdee001ce039c0238

def z660 : W := mkw 0xf8c5f5b1ef2b96a8 0x47f18beb63de572d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z661 : W := mkw 0x0412000000000000 0x0008240000000000 0x8e3f000000000001 0x611c7e0000000000

def z662 : W := mkw 0x857ab05bf0b5a310 0x2b0af560b7e16b46 0x8ffff8fff1ffe3fb 0xff1ffff1ffe3ffc7

def z663 : W := mkw 0x1200fe004241d808 0x402401fc008483b0 0x8e00ff0031c1fc1d 0x5d1c01fe006383f8

def z664 : W := mkw 0x857bb1dff0b7a791 0x3b0af763bfe16f4f 0x81fff8fff03fe3fb 0xbb03fff1ffe07fc7

def z665 : W := mkw 0x9169f5fbf233b7b0 0x2b22d3ebf7e4676f 0x81f8fffff031ffdf 0xbb03f1ffffe063ff

def z666 : W := mkw 0x20c521b0c62b16a0 0x00418a43618c562d 0x01c700f1ce3f1ff6 0x2c038e01e39c7e3f

def z667 : W := mkw 0x580044000b001008 0x44b0008800160020 0x700000000e000000 0x00e00000001c0000

def z668 : W := mkw 0xedff0181bdbe0484 0x8fdbfe03037b7c09 0xffff0781ffff1ff7 0xfffffe0f03fffe3f

def z669 : W := mkw 0xfffffffff63bb7b2 0xfbffffffffec776f 0xfffffffffe3fffff 0xfffffffffffc7fff

def z670 : W := mkw 0x8000900120008000 0x0300012002400100 0x800018003000e008 0x01000030006001c0

def z671 : W := mkw 0x0040001080200200 0x0000800021004004 0x01c000f0003003c2 0x20038001e0006007

def z672 : W := mkw 0x25fe000094bc0004 0x884bfc0001297800 0x71ff0001ce3e0061 0xeee3fe00039c7c00

def z673 : W := mkw 0x8169b1dbf033a790 0x2b02d363b7e0674f 0x81fffffff03fffff 0xff03ffffffe07fff

def z674 : W := mkw 0xda08fe037b51f908 0x47b411fc06f6a3f2 0xfe38ff8ffff1ffdf 0xfffc71ff1fffe3ff

def z675 : W := mkw 0x4e120a0400000002 0xd09c241408000000 0x0e00000000000000 0x001c000000000000

def z676 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0x7e00e701cfc01c04 0xc6fc01ce039f8038

def z677 : W := mkw 0xfba5dfec00000002 0xf3f74bbfd8000000 0x71c0fffe00000000 0x92e381fffc000000

def z678 : W := mkw 0xd800f4016b019008 0x47b001e802d60320 0xfe00e001ffc00001 0xcffc01c003ff8000

def z679 : W := mkw 0xda40fe11eb61da08 0x47b481fc23d6c3b4 0xffc0fff1fff1ffdf 0xffff81ffe3ffe3ff

def z680 : W := mkw 0x0168205bf031a310 0x2802d040b7e06346 0x01f800fff031e3da 0x2803f001ffe063c7

def z681 : W := mkw 0x8200ba016041c800 0x0304017402c08390 0x8e00ff01f1c1fc1d 0xdf1c01fe03e383f8

def z682 : W := mkw 0xdf32fe4d6b41d80a 0xf7be65fc9ad683b0 0xfe38ff0fffc1fc1d 0xdffc71fe1fff83f8

def z683 : W := mkw 0x7884442000000002 0xc0f1088840000000 0x7000000000000000 0x00e0000000000000

def z684 : W := mkw 0x02000a0000404800 0x0004001400008090 0x00001f000001fc1c 0x1000003e000003f8

def z685 : W := mkw 0x369f4fa610d66d81 0x106d3e9f4c21acdb 0xfffffffe31ffffff 0xfffffffffc63ffff

def z686 : W := mkw 0x8160b059e0218210 0x2b02c160b3c04304 0x01c0e0f1c03103d3 0xba0381c1e3806207

def z687 : W := mkw 0x688400000d080004 0x84d10800001a1000 0x700000000e000000 0x00e00000001c0000

def z688 : W := mkw 0x208501a0040a04a0 0x00410a0340081409 0x00070000000e0020 0x00000e0000001c00

def z689 : W := mkw 0x061a0a0010d44800 0x000c34140021a890 0x8e3f1f0031fffc7d 0x7d1c7e3e0063fff8

def z690 : W := mkw 0x7e974fa40b40580a 0xd4fd2e9f481680b0 0x7e0707000fc01c04 0x44fc0e0e001f8038

def z691 : W := mkw 0xe9e40001ad280004 0x8fd3c800035a5000 0xffc00001ffc00001 0xcfff800003ff8000

def z692 : W := mkw 0x20c50180842a0480 0x00418a0301085409 0x71c70781ce3f1ff7 0xfee38e0f039c7e3f

def z693 : W := mkw 0x10406410c2211200 0x002080c821844224 0x71c0e7f1ce311fd7 0xfee381cfe39c623f

def z694 : W := mkw 0xcf3a0a0739d46905 0x9f9e74140e73a8d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z695 : W := mkw 0x9000f40162019000 0x032001e802c40320 0xf000ff01fe01fc1d 0xdfe001fe03fc03f8

def z696 : W := mkw 0xedbe000010940000 0x83db7c0000212800 0xffff000031fe0061 0xeffffe000063fc00

def z697 : W := mkw 0x041b018610962581 0x100836030c212c4b 0x803f188e303fe3fb 0x39007e311c607fc7

def z698 : W := mkw 0xfffffffed6ff7fa3 0xf3fffffffdadfeff 0xffffffffffffffff 0xffffffffffffffff

def z699 : W := mkw 0x81600001a0200000 0x0b02c00003404000 0x01c00001c0000000 0x8203800003800000

def z700 : W := mkw 0xcf3a9a4e10d46903 0xf39e75349c21a8d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z701 : W := mkw 0x041a000210d66d81 0x000834000421acdb 0x8e3f000031ffffff 0x6d1c7e000063ffff

def z702 : W := mkw 0x02000a0000404800 0x0004001400008090 0x8e00180031c0e008 0x011c0030006381c0

def z703 : W := mkw 0xb1ecf47bf639b330 0x2b63d9e8f7ec7366 0xf1f8f8fffe31e3db 0xbbe3f1f1fffc63c7

def z704 : W := mkw 0xfff7dfec84280002 0xf3ffefbfd9085000 0xffffffffce3e0061 0xffffffffff9c7c00

def z705 : W := mkw 0x02009a4c00000002 0x7004013498000000 0x0000180e00000000 0x000000301c000000

def z706 : W := mkw 0xd80064016b011000 0x07b000c802d60220 0xfe00e701ffc11c15 0xdffc01ce03ff8238

def z707 : W := mkw 0xb1add5eb361ab5b0 0x2b635babd66c356b 0xf03f1f0e3e0efc2c 0x45e07e3e1c7c1df8

def z708 : W := mkw 0x1201fffc4243deaa 0x702403fff88487bd 0x0000fffe0001ff9e 0x100001fffc0003ff

def z709 : W := mkw 0x25b721ed6b41d80a 0xb44b6e43dad683b0 0x01ff00ffffc1fc1c 0x2c03fe01ffff83f8

def z710 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x8ff8f8fff1f1e3db 0xff1ff1f1ffe3e3c7

def z711 : W := mkw 0x00482013f9b5a314 0x0c00904027f36b46 0x00000001f1f1e3da 0x0800000003e3e3c7

def z712 : W := mkw 0xffb7dfed2900800a 0xf7ff6fbfda520100 0xfffffffe00000001 0xf3fffffffc000000

def z713 : W := mkw 0x36974fa406ce5ca1 0x106d2e9f480d9cb9 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z714 : W := mkw 0xdd3b65b17b9716a4 0x8fba76cb62f72e2d 0x8e38e7f031c11f96 0x111c71cfe063823f

def z715 : W := mkw 0x6cde0001bdbc0004 0x8cd9bc00037b7800 0x7fc70001fffe0061 0xeeff8e0003fffc00

def z716 : W := mkw 0x00482013fffdfb1c 0x0c00904027fffbf6 0x00000001fffffffe 0x0c00000003ffffff

def z717 : W := mkw 0x0120904800000000 0x2002412090000000 0x01f8f8fe00000000 0x3003f1f1fc000000

def z718 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe00ff01ffc1fc1c 0x93fc01fe03ff83f8

def z719 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c7e7f1ce3e1fe6 0xe6e38fcfe39c7c3f

def z720 : W := mkw 0x10416590c2231680 0x002082cb2184462d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z721 : W := mkw 0x36df6fb6d6ff7fa1 0x106dbedf6dadfeff 0x7e070701fffffffe 0x4cfc0e0e03ffffff

def z722 : W := mkw 0xedfe9049bdbc0004 0xafdbfd20937b7800 0xffffe071fffe0061 0xefffffc0e3fffc00

def z723 : W := mkw 0xf9a4d46800000002 0xe3f349a8d0000000 0x71f8e0fe00000000 0xa2e3f1c1fc000000

def z724 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0x7fffe7fe00000000 0xe2ffffcffc000000

def z725 : W := mkw 0x7e974fa40fce5ca9 0x54fd2e9f481f9cb9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z726 : W := mkw 0xcf72ba5cc62b16a2 0xf39ee574b98c562d 0x8e38180fce3f1ff6 0x0d1c70301f9c7e3f

def z727 : W := mkw 0xa5b791ec00000002 0xb34b6f23d8000000 0x01ffe0fe00000000 0xa203ffc1fc000000

def z728 : W := mkw 0x6c96b05a4d8da314 0xa4d92d60b49b1b46 0x7e07f8fe0fcfe3ba 0x54fc0ff1fc1f9fc7

def z729 : W := mkw 0x00482013f271fb18 0x0800904027e4e3f6 0x00000001f031ffde 0x0800000003e063ff

def z730 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe001f01ffc1fc1c 0x4dfc003e03ff83f8

def z731 : W := mkw 0xedfe005bbdbc2314 0xafdbfc00b77b7846 0xffff18ffffffe3fb 0xfffffe31ffffffc7

def z732 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81f8fffff031ffdf 0xff03f1ffffe063ff

def z733 : W := mkw 0x3697dfec00000002 0x706d2fbfd8000000 0xfffffffe00000001 0xf3fffffffc000000

def z734 : W := mkw 0x87339bcc00c64c81 0x330e673798018c99 0x8ffffffe01ce1c25 0xf71ffffffc039c38

def z735 : W := mkw 0xffb7dfec00c64c83 0xf3ff6fbfd8018c99 0xfffffffe01ff1ff7 0xfffffffffc03fe3f

def z736 : W := mkw 0xdf32de4c00000002 0xf3be65bc98000000 0xfff8fffe00000001 0xf3fff1fffc000000

def z737 : W := mkw 0x5a00fe016b41d808 0x44b401fc02d683b0 0x7e00ff01ffc1fc1c 0x5cfc01fe03ff83f8

def z738 : W := mkw 0x00482013f6ffffb1 0x0800904027edffff 0x00000001fffffffe 0x0c00000003ffffff

def z739 : W := mkw 0x25ff01b694be27a5 0x984bfe036d297c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z740 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe38ff8fffc1fc1d 0xfffc71ff1fff83f8

def z741 : W := mkw 0xedf60001adac0004 0x8fdbec00035b5800 0xffff0001cfce0021 0xe7fffe00039f9c00

def z742 : W := mkw 0xcd7a0001b9b40000 0x0f9af40003736800 0xffff0001fffe0061 0xeffffe0003fffc00

def z743 : W := mkw 0x7edf6fb7f031a312 0xd8fdbedf6fe06346 0x7e070701f031e3da 0x48fc0e0e03e063c7

def z744 : W := mkw 0x8120b05b6001a310 0x23024160b6c00346 0x81f8f8fff001e39b 0xbb03f1f1ffe003c7

def z745 : W := mkw 0x8168905a90302310 0x2b02d120b5206046 0x81f8f8fe3031e3db 0xbb03f1f1fc6063c7

def z746 : W := mkw 0xf9acd46a10d66d83 0xe3f359a8d421acdb 0x71c0e07031fffffe 0x8ee381c0e063ffff

def z747 : W := mkw 0x30cd65b3f63bb7b0 0x08619acb67ec776f 0x70070701fe3ffffe 0x4ce00e0e03fc7fff

def z748 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x00000001f000e008 0x0000000003e001c0

def z749 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8ffffffe31ffffff 0xff1ffffffc63ffff

def z750 : W := mkw 0xffb7dfed29000002 0xf7ff6fbfda520000 0xffffffffce000001 0xf3ffffffff9c0000

def z751 : W := mkw 0xedb600012d8c0004 0x87db6c00025b1800 0xffff0001ffce0021 0xeffffe0003ff9c00

def z752 : W := mkw 0xb5b7d5ec00000002 0xb36b6fabd8000000 0xf1fffffe00000001 0xf3e3fffffc000000

def z753 : W := mkw 0xdc1bf5877b97b589 0x57b837eb0ef72f6b 0x703fe08fce3e03e2 0xa2e07fc11f9c7c07

def z754 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfff8fffe00000000 0x93fff1fffc000000

def z755 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0x7fff0001cffe0060 0xe6fffe00039ffc00

def z756 : W := mkw 0x37b7dfec00000002 0xf06f6fbfd8000000 0x71fffffe00000001 0xf2e3fffffc000000

def z757 : W := mkw 0x8168b05ad0312300 0x2302d160b5a06246 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z758 : W := mkw 0xca00ba016941c800 0x0794017402d28390 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z759 : W := mkw 0x8168b05bfb31b318 0x2f02d160b7f66366 0x81f8f8fffe31e3db 0xbb03f1f1fffc63c7

def z760 : W := mkw 0xf9e4f479ef29922a 0xe7f3c9e8f3de5324 0x71c0e071ce000000 0x82e381c0e39c0000

def z761 : W := mkw 0x0000000000000000 0x0000000000000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z762 : W := mkw 0x00482012d031a310 0x0800904025a06346 0x000000000031e3da 0x00000000000063c7

def z763 : W := mkw 0x83209a4800000000 0x2306413490000000 0x8ff8fffe00000001 0xf31ff1fffc000000

def z764 : W := mkw 0xffb7dfec0040c80a 0xf3ff6fbfd8008190 0xfffffffe0000e009 0xf3fffffffc0001c0

def z765 : W := mkw 0xda006e016b41d808 0x47b400dc02d683b0 0xfe000701ffc1fc1d 0xcffc000e03ff83f8

def z766 : W := mkw 0x8168905bb030a310 0x2b02d120b7606146 0x81f8f8fe3030e3cb 0xb303f1f1fc6061c7

def z767 : W := mkw 0x8120904a00002100 0x2302412094000042 0x81f8f8fe0001e39b 0xb303f1f1fc0003c7

def z768 : W := mkw 0x00482013fb31b318 0x0c00904027f66366 0x00000001fe31e3da 0x0800000003fc63c7

def z769 : W := mkw 0x00482013fd39a314 0x0c00904027fa7346 0x00000001fe31e3da 0x0800000003fc63c7

def z770 : W := mkw 0xda004e012b405808 0x47b4009c025680b0 0xfe001f01ffc1fc1d 0xdffc003e03ff83f8

def z771 : W := mkw 0xedbe000139940000 0x87db7c0002732800 0xffff0001fffe0061 0xeffffe0003fffc00

def z772 : W := mkw 0xc968b05bf931a314 0xaf92d160b7f26346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z773 : W := mkw 0xffb7dfec0bc65c8b 0xf7ff6fbfd8178cb9 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z774 : W := mkw 0xe9ec0001bd380000 0x0fd3d800037a7000 0xffff0001fffe0061 0xeffffe0003fffc00

def z775 : W := mkw 0xf9e4f479ef299238 0x6ff3c9e8f3de5324 0x71c0e071ce000000 0x82e381c0e39c0000

def z776 : W := mkw 0xffb7dfed20008012 0xfbff6fbfda400100 0xfffffffe00000001 0xf3fffffffc000000

def z777 : W := mkw 0x36de6e36d6fd7b21 0x106dbcdc6dadfaf6 0xfff8f87fffc0e008 0x83fff1f0ffff81c0

def z778 : W := mkw 0xffb7dfec00424c82 0xf3ff6fbfd8008499 0xfffffffe31ffffff 0xfffffffffc63ffff

def z779 : W := mkw 0x24de0001bdbc0004 0x0c49bc00037b7800 0xffff0001fffe0061 0xeffffe0003fffc00

def z780 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c7e7f1ce3f1ff6 0xb2e38fcfe39c7e3f

def z781 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0x71c7e771ce3f1ff6 0xcee38fcee39c7e3f

def z782 : W := mkw 0xfdb7d5ec00000002 0xf3fb6fabd8000000 0x71ffe7fe00000001 0xf2e3ffcffc000000

def z783 : W := mkw 0xfba5dfec00000002 0xf3f74bbfd8000000 0xf1f8fffe00000001 0xb3e3f1fffc000000

def z784 : W := mkw 0xedfe0049bdbc0004 0xafdbfc00937b7800 0xffff00fffffe0061 0xeffffe01fffffc00

def z785 : W := mkw 0xffb6de6c00000002 0xf3ff6dbcd8000000 0xfffff87e00000001 0xe3fffff0fc000000

def z786 : W := mkw 0xda00fe4d6b41d80a 0x77b401fc9ad683b0 0xfe00ff0fffc1fc1d 0xdffc01fe1fff83f8

def z787 : W := mkw 0xedb791ec00000002 0xb3db6f23d8000000 0xfffff8fe00000001 0xf3fffff1fc000000

def z788 : W := mkw 0x8773bbdde0e7ce91 0x3b0ee777bbc1cf9d 0x0fc7e771c1ce1c24 0xc61f8fcee3839c38

def z789 : W := mkw 0xfe97dfa400000000 0x53fd2fbf48000000 0xfffffffe00000001 0xf3fffffffc000000

def z790 : W := mkw 0x5a486e13fb71fb18 0x4cb490dc27f6e3f6 0x7e000701fff1ffde 0x4cfc000e03ffe3ff

def z791 : W := mkw 0xffb7dfec048c0006 0xf3ff6fbfd8091800 0xfffffffe000e0021 0xf3fffffffc001c00

def z792 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe00ff81fff1ffdf 0xfffc01ff03ffe3ff

def z793 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffffffe00011c15 0xfffffffffc000238

def z794 : W := mkw 0xffb7dfed2b40d80a 0xf7ff6fbfda5681b0 0xfffffffe3fc0fc0d 0xf7fffffffc7f81f8

def z795 : W := mkw 0x00482013f0b5a310 0x0800904027e16b46 0x00000001f1ffe3fa 0x0c00000003e3ffc7

def z796 : W := mkw 0xffb7dfec06ce5ca3 0xf3ff6fbfd80d9cb9 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z797 : W := mkw 0xe9e40001ad280004 0x8fd3c800035a5000 0xffc70001fffe0061 0xefff8e0003fffc00

def z798 : W := mkw 0x1201ffde4243ff99 0x702403ffbc8487ff 0x0000fffe0001ff9e 0x100001fffc0003ff

def z799 : W := mkw 0xffb7dfec0dce4c87 0xf7ff6fbfd81b9c99 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z800 : W := mkw 0x83209a4c00000002 0x7306413498000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z801 : W := mkw 0x8168b05bf9b5a314 0x2f02d160b7f36b46 0x81f8f8fff1f1e3db 0xbb03f1f1ffe3e3c7

def z802 : W := mkw 0xedfe904bbdbca114 0xafdbfd20977b7942 0xffff188fffffe3fb 0xfffffe311fffffc7

def z803 : W := mkw 0xfdb745ec00000002 0xb3fb6e8bd8000000 0xffffe7fe00000001 0xf3ffffcffc000000

def z804 : W := mkw 0x7e974fa400000002 0xd0fd2e9f48000000 0xfffffffe00000001 0xf3fffffffc000000

def z805 : W := mkw 0xec9600012d8c0004 0x87d92c00025b1800 0x7e070001cfce0020 0xc6fc0e00039f9c00

def z806 : W := mkw 0xb7b7dfec00000002 0xf36f6fbfd8000000 0x81fffffe00000001 0xb303fffffc000000

def z807 : W := mkw 0xc920904800000002 0xe392412090000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z808 : W := mkw 0x6cd600008dac0004 0x84d9ac00011b5800 0x7fc70001cfce0020 0xc6ff8e00039f9c00

def z809 : W := mkw 0x02090b8210526d80 0x000412170420a4db 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z810 : W := mkw 0x00482013f971eb18 0x0c00904027f2e3d6 0x00000001f1f1e3da 0x0800000003e3e3c7

def z811 : W := mkw 0x061a0a0210d46900 0x000c34140421a8d2 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z812 : W := mkw 0x6cde2013fdbda314 0x8cd9bc4027fb7b46 0x7e070001ffffe3fa 0x4cfc0e0003ffffc7

def z813 : W := mkw 0x1249dfedbdbc0006 0x7c2493bfdb7b7800 0x0000fffffffe0060 0x1c0001fffffffc00

def z814 : W := mkw 0xf9a5d5e800000002 0xe3f34babd0000000 0xf1fffffe00000001 0xf3e3fffffc000000

def z815 : W := mkw 0xffb7dfec00404802 0xf3ff6fbfd8008090 0xfffffffe01c01c05 0xf7fffffffc038038

def z816 : W := mkw 0x35b7d5ec00000002 0xf06b6fabd8000000 0x01ffe0fe00000000 0x2003ffc1fc000000

def z817 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xffffffffce000001 0xffffffffff9c0000

def z818 : W := mkw 0xebe50b87ad6a6d85 0x9fd7ca170f5ad4db 0x71c01f8fce01ff9e 0x92e3803f1f9c03ff

def z819 : W := mkw 0x7e974fa40f4a5caa 0xd4fd2e9f481e94b9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z820 : W := mkw 0xc8482013f931a310 0x0f90904027f26346 0xfe000001fff1e3db 0xcffc000003ffe3c7

def z821 : W := mkw 0xeac59bb1ad6acea8 0x47d58b37635ad59d 0x8fc718f031fee3ea 0x211f8e31e063fdc7

def z822 : W := mkw 0xcd3a000139940004 0x8f9a740002732800 0xfe3f0001fffe0061 0xeffc7e0003fffc00

def z823 : W := mkw 0x12016fb442435ea1 0x102402df688486bd 0x0000e7f000011f96 0x100001cfe000023f

def z824 : W := mkw 0x0120004800000000 0x2002400090000000 0x01f8e0fe00000001 0xb203f1c1fc000000

def z825 : W := mkw 0x00482013f931a310 0x0c00904027f26346 0x00000001fff1e3da 0x0c00000003ffe3c7

def z826 : W := mkw 0xedfe0003bdbc2104 0x8fdbfc00077b7842 0xffff008ffffe03e3 0xeffffe011ffffc07

def z827 : W := mkw 0xc968b05bf931a318 0x6f92d160b7f26346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z828 : W := mkw 0xedfe9049bdbc0004 0xafdbfd20937b7800 0xffff180ffffe0061 0xeffffe301ffffc00

def z829 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0xf1c7fff1fe3fffff 0xffe38fffe3fc7fff

def z830 : W := mkw 0x02482a13f071eb10 0x0804905427e0e3d6 0x8e001f01f1f1ffdf 0x5d1c003e03e3e3ff

def z831 : W := mkw 0xc800000129000000 0x0790000002520000 0xfe070001fffe0061 0xeffc0e0003fffc00

def z832 : W := mkw 0xe8cc0001bdbc0004 0x0fd19800037b7800 0xffc70001fffe0061 0xefff8e0003fffc00

def z833 : W := mkw 0xcb209a492940c808 0x6796413492528190 0x8ff8f8fe31c0e009 0xb31ff1f1fc6381c0

def z834 : W := mkw 0x06130b8400000000 0x100c261708000000 0x8ffffffe00000001 0xf31ffffffc000000

def z835 : W := mkw 0xe88400012d080000 0x07d10800025a1000 0xfe070001ffce0021 0xcffc0e0003ff9c00

def z836 : W := mkw 0x1201fffe4243ffb1 0x302403fffc8487ff 0x0000fffe0001ff9e 0x100001fffc0003ff

def z837 : W := mkw 0x1201ffb64243ffa9 0x502403ff6c8487ff 0x0000fffe0001ff9e 0x100001fffc0003ff

def z838 : W := mkw 0xda00fe116b41da08 0x47b401fc22d683b4 0xfe00fff1ffc1ff9f 0xdffc01ffe3ff83ff

def z839 : W := mkw 0xa1a591e800000000 0x23434b23d0000000 0x81fff8fe00000001 0xb303fff1fc000000

def z840 : W := mkw 0x37fefe00d6fdd80c 0xc86ffdfc01adfbb0 0x01ffff00003ffc7c 0x3003fffe00007ff8

def z841 : W := mkw 0xecde0001bdbc0004 0x8fd9bc00037b7800 0xfe070001fffe0061 0xcffc0e0003fffc00

def z842 : W := mkw 0xedfe905bbdbc2314 0xafdbfd20b77b7846 0xfffff8fffffe03e3 0xfffffff1fffffc07

def z843 : W := mkw 0x5a006e004b415808 0x44b400dc009682b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z844 : W := mkw 0x8120904800000000 0x2302412090000000 0x81f8f8fe3001e019 0xbb03f1f1fc6003c0

def z845 : W := mkw 0x0168b05ad031a310 0x2802d160b5a06346 0x01f8f8ffc031e3db 0xba03f1f1ff8063c7

def z846 : W := mkw 0xffb7dfec060a14a2 0xf3ff6fbfd80c1429 0xfffffffe0e3f1ff7 0xfffffffffc1c7e3f

def z847 : W := mkw 0xedfe004bbdbc2114 0xafdbfc00977b7842 0xffff000ffffe0061 0xeffffe001ffffc00

def z848 : W := mkw 0x8168b05bf0b5a310 0x2b02d160b7e16b46 0x81f8f8fff1ffe3fb 0xbf03f1f1ffe3ffc7

def z849 : W := mkw 0xdb21dfec00000002 0x73b643bfd8000000 0xfff8fffe00000001 0xf3fff1fffc000000

def z850 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff0081ffff03f3 0xfffffe0103fffe07

def z851 : W := mkw 0xfba4de6800000002 0xe3f749bcd0000000 0xfff8fffe00000001 0xf3fff1fffc000000

def z852 : W := mkw 0x02000a0000404800 0x0004001400008090 0xfe001f01ffc1fc1d 0xdffc003e03ff83f8

def z853 : W := mkw 0x8160b05ac021a310 0x2302c160b5804346 0x81f8f8ffc031e3db 0xbb03f1f1ff8063c7

def z854 : W := mkw 0x5a006e016b41d808 0x44b400dc02d683b0 0x7e00e701ffc1fc1d 0xdefc01ce03ff83f8

def z855 : W := mkw 0x00482013f0b7a791 0x0800904027e16f4f 0x00000001f03fe3fa 0x0800000003e07fc7

def z856 : W := mkw 0xedfe905bbdbca314 0xafdbfd20b77b7946 0xffff18fffffee3eb 0xeffffe31fffffdc7

def z857 : W := mkw 0xffb7dfed20000002 0xf3ff6fbfda400000 0xfffffffff0000001 0xfbffffffffe00000

def z858 : W := mkw 0xffb7dfec00c64c83 0xf3ff6fbfd8018c99 0xfffffffe31cffc3d 0xfffffffffc639ff8

def z859 : W := mkw 0xdb20fe016b41d808 0x47b641fc02d683b0 0xfff8ff01ffc1fc1d 0xfffff1fe03ff83f8

def z860 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0xf1ffffffce3f1ff7 0xffe3ffffff9c7e3f

def z861 : W := mkw 0x00482013f439a310 0x0800904027e87346 0x00000001fe3fe3fa 0x0c00000003fc7fc7

def z862 : W := mkw 0x8120904920000000 0x2302412092400000 0x81f8f8fff0000001 0xbb03f1f1ffe00000

def z863 : W := mkw 0x9120d44800000000 0x232241a890000000 0xf1f8fffe00000001 0xf3e3f1fffc000000

def z864 : W := mkw 0x00482012d0312310 0x0800904025a06246 0x00000001c03103d2 0x0800000003806207

def z865 : W := mkw 0x87329a4c00000000 0x330e653498000000 0x8ff8f8fe00000001 0xb31ff1f1fc000000

def z866 : W := mkw 0xffb7dfec0b40580a 0xf7ff6fbfd81680b0 0xfffffffe3fc1fc1d 0xfffffffffc7f83f8

def z867 : W := mkw 0xfdb6d46c00000002 0xf3fb6da8d8000000 0x71f8e07e00000000 0x82e3f1c0fc000000

def z868 : W := mkw 0x36974fa400c64c81 0x106d2e9f48018c99 0x7e07070001ce1c24 0x44fc0e0e00039c38

def z869 : W := mkw 0x6dfe0001bdbc0004 0x8cdbfc00037b7800 0x7fff0001fffe0060 0x6cfffe0003fffc00

def z870 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff0001fffe0060 0xa3fffe0003fffc00

def z871 : W := mkw 0xda006e016b415800 0x07b400dc02d682b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z872 : W := mkw 0xfdb7d5e800000000 0xa3fb6fabd0000000 0xfffffffe00000001 0xf3fffffffc000000

def z873 : W := mkw 0x20c52190c42b0680 0x00418a432188560d 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z874 : W := mkw 0x1200fe004241d808 0x402401fc008483b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z875 : W := mkw 0xcd32904800000000 0xa39a652090000000 0x8ff8f8fe00000001 0xb31ff1f1fc000000

def z876 : W := mkw 0xda00fe496b41d808 0x67b401fc92d683b0 0xfe00ffffffc1fc1d 0xdffc01ffffff83f8

def z877 : W := mkw 0x812191c800000000 0x2302432390000000 0x81fffffe00000001 0xf303fffffc000000

def z878 : W := mkw 0x12006e016b41d808 0x042400dc02d683b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z879 : W := mkw 0x00482012d63b37a0 0x0000904025ac766f 0x00000001fe3ffffe 0x0c00000003fc7fff

def z880 : W := mkw 0x9121d5e800000000 0x232243abd0000000 0x81f8fffe00000001 0xb303f1fffc000000

def z881 : W := mkw 0x5b684e5a9b707b18 0x6cb6d09cb536e0f6 0x7ff807fe0ff01fc6 0x64fff00ffc1fe03f

def z882 : W := mkw 0x25fe000094bc0004 0x884bfc0001297800 0xffff0001fffe0061 0xeffffe0003fffc00

def z883 : W := mkw 0x853391cc00000000 0x330a672398000000 0x81fff8fe00000001 0xb303fff1fc000000

def z884 : W := mkw 0xffb7dfec00020482 0xf3ff6fbfd8000409 0xfffffffe000e1c25 0xf7fffffffc001c38

def z885 : W := mkw 0xedfe9001bdbc0004 0x8fdbfd20037b7800 0xfffff801fffe0061 0xfffffff003fffc00

def z886 : W := mkw 0x8120904800000000 0x2302412090000000 0x81f8f8fe003103d3 0xbb03f1f1fc006207

def z887 : W := mkw 0xfba5dfe800000000 0x63f74bbfd0000000 0xfffffffe00000001 0xf3fffffffc000000

def z888 : W := mkw 0x12016fb042435ea8 0x402402df608486bd 0x0000e7f000011f96 0x100001cfe000023f

def z889 : W := mkw 0xda00fe696b41d80a 0x67b401fcd2d683b0 0xfe00ff71ffc1fc1d 0xdffc01fee3ff83f8

def z890 : W := mkw 0x00482013ffbfb7b4 0x0c00904027ff7f6f 0x00000001fffffffe 0x0c00000003ffffff

def z891 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8e3f1f0e31fffffe 0x4d1c7e3e1c63ffff

def z892 : W := mkw 0xffb7dfec040a04a2 0xf3ff6fbfd8081409 0xfffffffe000e0021 0xf3fffffffc001c00

def z893 : W := mkw 0xcf3a9a4f39d46907 0xff9e75349e73a8d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z894 : W := mkw 0x25ff01ee94be2587 0xb84bfe03dd297c4b 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z895 : W := mkw 0xd80064016b41d808 0x07b000c802d683b0 0xfe00e701ffc1fc1d 0xdffc01ce03ff83f8

def z896 : W := mkw 0xedfe0011bdbc0204 0x8fdbfc00237b7804 0xffff00f1fffe03e3 0xeffffe01e3fffc07

def z897 : W := mkw 0xf9a4d46800000002 0xe3f349a8d0000000 0xf1f8f87e00000000 0x83e3f1f0fc000000

def z898 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xffffff7e00000000 0xc3fffffefc000000

def z899 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffffffe003e0061 0xfffffffffc007c00

def z900 : W := mkw 0xffb7dfec09000002 0xf7ff6fbfd8120000 0xfffffffe0fc00001 0xf7fffffffc1f8000

def z901 : W := mkw 0xda00fe0042415800 0x43b401fc008482b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z902 : W := mkw 0x8048b013f031a310 0x0b00916027e06346 0x80001801f031e3da 0x0900003003e063c7

def z903 : W := mkw 0x00482013f233b7b0 0x0800904027e4676f 0x00000001f031ffde 0x0800000003e063ff

def z904 : W := mkw 0x00482013f033a790 0x0800904027e0674f 0x00000001f03ffffe 0x0c00000003e07fff

def z905 : W := mkw 0x1201ff844243dc89 0x502403ff088487b9 0x0000ff000001fc1c 0x100001fe000003f8

def z906 : W := mkw 0x1201fffa4243ffb8 0x602403fff48487ff 0x0000fffe0001ff9e 0x100001fffc0003ff

def z907 : W := mkw 0xffb7dfec020214a2 0xf3ff6fbfd8040429 0xfffffffe00001c05 0xf3fffffffc000038

def z908 : W := mkw 0xdb20de480b405808 0x67b641bc901680b0 0xfff8fffe0fc01c05 0xf7fff1fffc1f8038

def z909 : W := mkw 0xedfe0031bdbc0224 0x8fdbfc00637b7804 0xffff0071fffe0061 0xeffffe00e3fffc00

def z910 : W := mkw 0x81682013f0312300 0x0b02d04027e06246 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z911 : W := mkw 0x7e974fa40dce4c87 0xd4fd2e9f481b9c99 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z912 : W := mkw 0xedfe0003bdbc2104 0x8fdbfc00077b7842 0xffff180ffffee069 0xeffffe301ffffdc0

def z913 : W := mkw 0xffb7dfec00404802 0xf3ff6fbfd8008090 0xfffffffe0001fc1d 0xf3fffffffc0003f8

def z914 : W := mkw 0xdb20fe496b41d80a 0xe7b641fc92d683b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z915 : W := mkw 0xedfe0059bdbc0214 0xafdbfc00b37b7804 0xffff0071fffe0061 0xeffffe00e3fffc00

def z916 : W := mkw 0x00482013f231b310 0x0800904027e46366 0x00000001fe31ffde 0x0c00000003fc63ff

def z917 : W := mkw 0xffb6de4800000000 0xe3ff6dbc90000000 0xfffffffe00000001 0xf3fffffffc000000

def z918 : W := mkw 0xc920904800000000 0x2392412090000000 0xfff8f8fe00000001 0xf3fff1f1fc000000

def z919 : W := mkw 0x8168b05bf4bda314 0x2b02d160b7e97b46 0x81f8f8fff03fe3fb 0xbb03f1f1ffe07fc7

def z920 : W := mkw 0x35b745ec00000002 0xb06b6e8bd8000000 0x71ffe0fe00000000 0xa2e3ffc1fc000000

def z921 : W := mkw 0x0048b05ad031a310 0x20009160b5a06346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z922 : W := mkw 0x25ff01fa94be27b4 0xa84bfe03f5297c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z923 : W := mkw 0x00482012d0f76f81 0x0000904025a1eedf 0x00000001f1fffffe 0x0c00000003e3ffff

def z924 : W := mkw 0xefb69a4c00000002 0xf3df6d3498000000 0xfffff8fe00000001 0xf3fffff1fc000000

def z925 : W := mkw 0xb1a4d46800000000 0x236349a8d0000000 0xf1f8f8fe00000001 0xb3e3f1f1fc000000

def z926 : W := mkw 0xedfe0003bdbc2104 0x8fdbfc00077b7842 0xffff0001ffffe3fb 0xeffffe0003ffffc7

def z927 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff1801ffffe079 0xfffffe3003ffffc0

def z928 : W := mkw 0xffb7dfed2940c80a 0xf7ff6fbfda528190 0xffffffffffc0e009 0xffffffffffff81c0

def z929 : W := mkw 0x812191ec00000002 0x33024323d8000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z930 : W := mkw 0x9320de4800000000 0x632641bc90000000 0x81f8fffe00000001 0xb303f1fffc000000

def z931 : W := mkw 0x12016fb042435ea0 0x002402df608486bd 0x0000fff00001ff9e 0x100001ffe00003ff

def z932 : W := mkw 0xfdb7d5ec00000002 0xf3fb6fabd8000000 0xffffe0fe00000001 0xe3ffffc1fc000000

def z933 : W := mkw 0xffb7dfed29000002 0xf7ff6fbfda520000 0xfffffffe31c00001 0xf3fffffffc638000

def z934 : W := mkw 0xffb7dfec00c44803 0xf3ff6fbfd8018890 0xfffffffe01c00001 0xf3fffffffc038000

def z935 : W := mkw 0xcf339bcc00000002 0xf39e673798000000 0x8ffffffe00000001 0xf31ffffffc000000

def z936 : W := mkw 0xffb7dfec00020482 0xf3ff6fbfd8000409 0xfffffffe003e03e3 0xf3fffffffc007c07

def z937 : W := mkw 0x0168205ad0312310 0x2802d040b5a06246 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z938 : W := mkw 0xffb7dfec0240580a 0xf3ff6fbfd80480b0 0xfffffffe00001c05 0xf3fffffffc000038

def z939 : W := mkw 0xda00de0129404800 0x47b401bc02528090 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z940 : W := mkw 0x5a006e016b41d808 0x44b400dc02d683b0 0xfe001f01ffc1fc1d 0x5dfc003e03ff83f8

def z941 : W := mkw 0xedf60001adac0004 0x8fdbec00035b5800 0xffc70001ffce0021 0xcfff8e0003ff9c00

def z942 : W := mkw 0x0008000210102100 0x0000100004202042 0x81f8f8fe3031e3db 0xbb03f1f1fc6063c7

def z943 : W := mkw 0x7e974fa406ce5ca3 0xd0fd2e9f480d9cb9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z944 : W := mkw 0xda00fe316b41da28 0x47b401fc62d683b4 0xfe00ff71ffc1fc1d 0xdffc01fee3ff83f8

def z945 : W := mkw 0x1201fffe42437fa3 0x702403fffc8486ff 0x0000fffe0001ff9e 0x100001fffc0003ff

def z946 : W := mkw 0x8532904800000000 0x230a652090000000 0x8ffff8fe00000001 0xf31ffff1fc000000

def z947 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff0701ffff1c75 0xfffffe0e03fffe38

def z948 : W := mkw 0xedfe0013bdbc2314 0x8fdbfc00277b7846 0xffff0001fffe03e3 0xeffffe0003fffc07

def z949 : W := mkw 0x7e974fa400424c83 0xd0fd2e9f48008499 0x7e07070000001c04 0x40fc0e0e00000038

def z950 : W := mkw 0x00482013f071eb10 0x0800904027e0e3d6 0x00000001f1f1ffde 0x0c00000003e3e3ff

def z951 : W := mkw 0x8128b05b7011a310 0x2b025160b6e02346 0x81f8f8fe3001e39b 0xb303f1f1fc6003c7

def z952 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff188ffffe0061 0xfffffe311ffffc00

def z953 : W := mkw 0xedfe0003bdbca114 0x8fdbfc00077b7942 0xffff0001fffee069 0xeffffe0003fffdc0

def z954 : W := mkw 0xedfe000094bc0000 0x83dbfc0001297800 0xffff0001fffe0061 0xeffffe0003fffc00

def z955 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xffc0fff1ffc1fc1d 0xffff81ffe3ff83f8

def z956 : W := mkw 0xedfe904bbdbca114 0xafdbfd20977b7942 0xfffff8fffffee069 0xfffffff1fffffdc0

def z957 : W := mkw 0xffb7dfed2d8c0006 0xf7ff6fbfda5b1800 0xffffffffffce0021 0xffffffffffff9c00

def z958 : W := mkw 0x6cd60001adac0004 0x8cd9ac00035b5800 0x7e070001cfce0020 0x44fc0e00039f9c00

def z959 : W := mkw 0xffb7dfec00020482 0xf3ff6fbfd8000409 0xfffffffe00011f97 0xf3fffffffc00023f

def z960 : W := mkw 0x308d45a210d66d81 0x00611a8b4421acdb 0x71c7e7f031ffffff 0xfee38fcfe063ffff

def z961 : W := mkw 0x8048b013f031a300 0x0300916027e06346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z962 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xfe3f0001fffe0060 0x4dfc7e0003fffc00

def z963 : W := mkw 0xdb20fe496b41d808 0x67b641fc92d683b0 0xfe38ff0fffc1fc1d 0xdffc71fe1fff83f8

def z964 : W := mkw 0xffb74fa400000000 0x93ff6e9f48000000 0xfffffffe00000001 0xf3fffffffc000000

def z965 : W := mkw 0x24d6000084ac0000 0x0049ac0001095800 0x7fc70001cffe0061 0xeeff8e00039ffc00

def z966 : W := mkw 0x7fb7dfec00000002 0xf0ff6fbfd8000000 0x7ffffffe00000000 0x70fffffffc000000

def z967 : W := mkw 0xedbe00013d9c0004 0x8fdb7c00027b3800 0xfe3f0001ffce0021 0xcffc7e0003ff9c00

def z968 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffffffe003103d3 0xfbfffffffc006207

def z969 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x00000081f031e3db 0x3800000103e063c7

def z970 : W := mkw 0x00482013f43ba7b0 0x0800904027e8774f 0x00000001f03fe3fa 0x0800000003e07fc7

def z971 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x00000001c03003c2 0x0000000003806007

def z972 : W := mkw 0x8168b05bf931a310 0x2f02d160b7f26346 0x81f8f8fffff1e3db 0xbf03f1f1ffffe3c7

def z973 : W := mkw 0x9120d46800000002 0x632241a8d0000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z974 : W := mkw 0xb3a5dfec00000002 0x73674bbfd8000000 0xf1fffffe00000001 0xf3e3fffffc000000

def z975 : W := mkw 0xedf600008dac0004 0x87dbec00011b5800 0xffff0001cffe0061 0xeffffe00039ffc00

def z976 : W := mkw 0xda00fe596b41da18 0x67b401fcb2d683b4 0xfe00ff71ffc1fc1d 0xdffc01fee3ff83f8

def z977 : W := mkw 0xdb20fe496b41d808 0x67b641fc92d683b0 0xffc0ff71ffc1fc1d 0xdfff81fee3ff83f8

def z978 : W := mkw 0x308565a042031480 0x00610acb40840629 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z979 : W := mkw 0xd800f4016b019000 0x07b001e802d60320 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z980 : W := mkw 0xffb7dfec00404802 0xf3ff6fbfd8008090 0xfffffffe31c0e009 0xf3fffffffc6381c0

def z981 : W := mkw 0x00482013f639b330 0x0800904027ec7366 0x00000001fe31e3da 0x0800000003fc63c7

def z982 : W := mkw 0x83209a4800404800 0x2306413490008090 0x8ff8fffe31c1fc1d 0xff1ff1fffc6383f8

def z983 : W := mkw 0x35b745ec00000002 0xb06b6e8bd8000000 0x01ffe7fe00000000 0x3003ffcffc000000

def z984 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe07ff01fffffc7d 0xfffc0ffe03fffff8

def z985 : W := mkw 0x00492193f033a790 0x0800924327e0674f 0x00070781f03fffff 0x7c000e0f03e07fff

def z986 : W := mkw 0xedfe9049bdbc8014 0xafdbfd20937b7900 0xffff0001fffe0061 0xeffffe0003fffc00

def z987 : W := mkw 0x30c565b0c62b16a0 0x00618acb618c562d 0xffc7e7f1ffff1ff7 0xffff8fcfe3fffe3f

def z988 : W := mkw 0x8160b059e0218200 0x2302c160b3c04304 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z989 : W := mkw 0x8120904920008000 0x2302412092400100 0x81f8f8fe3000e009 0xb303f1f1fc6001c0

def z990 : W := mkw 0x00482013fbf7ff99 0x0c00904027f7efff 0x00000001fffffffe 0x0c00000003ffffff

def z991 : W := mkw 0x00482013fdffef95 0x0c00904027fbffdf 0x00000001fffffffe 0x0c00000003ffffff

def z992 : W := mkw 0x1201ffee4243fd8b 0x702403ffdc8487fb 0x0000fffe0001ff9e 0x100001fffc0003ff

def z993 : W := mkw 0x1201ffa04243dca8 0x402403ff408487b9 0x0000ff000001fc1c 0x100001fe000003f8

def z994 : W := mkw 0xedfe004dbdbc0006 0xbfdbfc009b7b7800 0xffff000ffffe0061 0xeffffe001ffffc00

def z995 : W := mkw 0xffb6de6c00000002 0xf3ff6dbcd8000000 0xfff8ff7e00000001 0xd3fff1fefc000000

def z996 : W := mkw 0xecde0001bdbc0000 0x07d9bc00037b7800 0xffff0001fffe0061 0xeffffe0003fffc00

def z997 : W := mkw 0xcf3a9a4b39d4e91c 0xef9e75349673a9d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z998 : W := mkw 0x25ff01fe94be27b1 0x384bfe03fd297c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z999 : W := mkw 0x065b2b97f0f7ef91 0x180cb6572fe1efdf 0x0e070701f1fffffe 0x4c1c0e0e03e3ffff

def z1000 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0x71fffffe00000000 0xb2e3fffffc000000

def z1001 : W := mkw 0xa1a4906800000002 0xa3434920d0000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z1002 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffffe0f1fffe0061 0xffffffc1e3fffc00

def z1003 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81fff8fff03fe3fb 0xff03fff1ffe07fc7

def z1004 : W := mkw 0x349745a400000000 0x10692e8b48000000 0x71ffe7fe00000001 0xf2e3ffcffc000000

def z1005 : W := mkw 0x8168b05bf231b310 0x2b02d160b7e46366 0x81f8f8fffe31ffdf 0xbf03f1f1fffc63ff

def z1006 : W := mkw 0xffb7dfec00860483 0xf3ff6fbfd8010c09 0xfffffffe000e0021 0xf3fffffffc001c00

def z1007 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffffffe31c00001 0xfffffffffc638000

def z1008 : W := mkw 0x00482013f073ef91 0x0800904027e0e7df 0x00000001f031ffde 0x0800000003e063ff

def z1009 : W := mkw 0xc920904929000000 0x2792412092520000 0xfff8f8ffffc00001 0xfffff1f1ffff8000

def z1010 : W := mkw 0xffb7dfed29404802 0xf7ff6fbfda528090 0xffffffffffc1fc1d 0xffffffffffff83f8

def z1011 : W := mkw 0xedfe904bbdbc2104 0xafdbfd20977b7842 0xfffff8ffffffe3fb 0xfffffff1ffffffc7

def z1012 : W := mkw 0x1201ff804243dc88 0x402403ff008487b9 0x0000ff800001ff9e 0x100001ff000003ff

def z1013 : W := mkw 0xedf60001adac0004 0x8fdbec00035b5800 0x7fc70001cffe0061 0xeeff8e00039ffc00

def z1014 : W := mkw 0xc968b05bf931a310 0x2f92d160b7f26346 0xf1f8f8fffe31e3db 0xbbe3f1f1fffc63c7

def z1015 : W := mkw 0x80482013f031a310 0x0b00904027e06346 0x80000001f031e3db 0x8b00000003e063c7

def z1016 : W := mkw 0xcf3a9a4f39d4e90b 0xf79e75349e73a9d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z1017 : W := mkw 0x25b701ec00000002 0xb04b6e03d8000000 0x01ffe0fe00000001 0xb203ffc1fc000000

def z1018 : W := mkw 0x8120904800000000 0x2302412090000000 0x81f8f87e00000000 0x8303f1f0fc000000

def z1019 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffff8fe00000000 0xa3fffff1fc000000

def z1020 : W := mkw 0xffb7dfec0b00100a 0xf7ff6fbfd8160020 0xfffffffe0e000001 0xf3fffffffc1c0000

def z1021 : W := mkw 0x25ff01fe94be27a3 0xb04bfe03fd297c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z1022 : W := mkw 0x06130b8400424c80 0x100c261708008499 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z1023 : W := mkw 0xca48ba13f971eb18 0x4f94917427f2e3d6 0x8e001801f1f1e3da 0x091c003003e3e3c7

def z1024 : W := mkw 0xecd60001adac0004 0x87d9ac00035b5800 0xffc70001fffe0061 0xefff8e0003fffc00

def z1025 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0xfe00ff01ffc0fc0c 0xc7fc01fe03ff81f8

def z1026 : W := mkw 0xffb7dfed20008002 0xf3ff6fbfda400100 0xfffffffe3000e009 0xf3fffffffc6001c0

def z1027 : W := mkw 0x6c9600012d8c0004 0x84d92c00025b1800 0x7e070001ffce0020 0x4cfc0e0003ff9c00

def z1028 : W := mkw 0x00482013f0f5eb11 0x0800904027e1ebd6 0x00000001f1f1e3da 0x0800000003e3e3c7

def z1029 : W := mkw 0xcf329a4c00000002 0xf39e653498000000 0x8ff8f87e00000000 0x831ff1f0fc000000

def z1030 : W := mkw 0xffb7dfec04080002 0xf3ff6fbfd8081000 0xfffffffe0e0e0021 0xf7fffffffc1c1c00

def z1031 : W := mkw 0xffb7dfed2940c80a 0xf7ff6fbfda528190 0xfffffffe31c1fc1d 0xfffffffffc6383f8

def z1032 : W := mkw 0x00482013ffffffa9 0x0400904027ffffff 0x00000001fffffffe 0x0c00000003ffffff

def z1033 : W := mkw 0xdf33dfec00000002 0xf3be67bfd8000000 0x8ff8fffe00000001 0xb31ff1fffc000000

def z1034 : W := mkw 0xc968b05bf931a310 0x2f92d160b7f26346 0x8ff8f8fff1f1e3db 0xbb1ff1f1ffe3e3c7

def z1035 : W := mkw 0x68c400008d280000 0x04d18800011a5000 0x7fc70001cffe0061 0xeeff8e00039ffc00

def z1036 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0x8ffffffe00000000 0x311ffffffc000000

def z1037 : W := mkw 0x9200fe016241d800 0x032401fc02c483b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z1038 : W := mkw 0xffb7dfec02001002 0xf3ff6fbfd8040020 0xfffffffe0e001c05 0xf7fffffffc1c0038

def z1039 : W := mkw 0x31a545e800000000 0x20634a8bd0000000 0x71ffe7fe00000001 0xf2e3ffcffc000000

def z1040 : W := mkw 0x0120b05a4001a310 0x20024160b4800346 0x01f8f8fe0001e39a 0x3003f1f1fc0003c7

def z1041 : W := mkw 0xedfe0007bdbc2105 0x9fdbfc000f7b7842 0xffff000ffffe0061 0xeffffe001ffffc00

def z1042 : W := mkw 0xcc12000129840000 0x0798240002530800 0xfe070001ffce0021 0xcffc0e0003ff9c00

def z1043 : W := mkw 0x8168b05bfd39a314 0x2f02d160b7fa7346 0x81f8f8fffe31e3db 0xbb03f1f1fffc63c7

def z1044 : W := mkw 0x8532904c00000002 0xb30a652098000000 0x81f8f8fe00000001 0xb303f1f1fc000000

def z1045 : W := mkw 0xffb7dfec0fcc580e 0xf7ff6fbfd81f98b0 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z1046 : W := mkw 0xb7b7dfec00000000 0x336f6fbfd8000000 0xfffffffe00000001 0xf3fffffffc000000

def z1047 : W := mkw 0x00482012d63b37b0 0x0800904025ac766f 0x00000001ce3f1ff6 0x0c000000039c7e3f

def z1048 : W := mkw 0x0168b05bf031a310 0x2802d160b7e06346 0x01f8f8fff031e3da 0x3803f1f1ffe063c7

def z1049 : W := mkw 0xffb7dfec06081022 0xf3ff6fbfd80c1020 0xfffffffe0e000001 0xf3fffffffc1c0000

def z1050 : W := mkw 0xffb7dfec0d080006 0xf7ff6fbfd81a1000 0xfffffffe0e000001 0xf3fffffffc1c0000

def z1051 : W := mkw 0xcc5a0001bdbc0004 0x0f98b400037b7800 0xfe3f0001fffe0061 0xeffc7e0003fffc00

def z1052 : W := mkw 0x6c9600000d8c0004 0x84d92c00001b1800 0x7e070001cfce0021 0xcefc0e00039f9c00

def z1053 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0xfe3f1f8fffffffff 0xfffc7e3f1fffffff

def z1054 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81f8f8fe3031e3da 0x3103f1f1fc6063c7

def z1055 : W := mkw 0x00482013f4bda314 0x0800904027e97b46 0x00000001f03fe3fa 0x0800000003e07fc7

def z1056 : W := mkw 0xc968b05bfdbda314 0x2f92d160b7fb7b46 0xfff8f8ffffffe3fb 0xfffff1f1ffffffc7

def z1057 : W := mkw 0xda00fe016b41d808 0x47b401fc02d683b0 0x7e00e701ffc1fc1c 0xcefc01ce03ff83f8

def z1058 : W := mkw 0xdf33dfcc00000000 0x73be67bf98000000 0xfffffffe00000001 0xf3fffffffc000000

def z1059 : W := mkw 0xffb7dfec00424c83 0xf3ff6fbfd8008499 0xfffffffe00001c05 0xf3fffffffc000038

def z1060 : W := mkw 0xedfe0069bdbc0006 0xafdbfc00d37b7800 0xffff0071fffe0061 0xeffffe00e3fffc00

def z1061 : W := mkw 0xedfe9001bdbc8004 0x8fdbfd20037b7900 0xffff1801fffee069 0xeffffe3003fffdc0

def z1062 : W := mkw 0x30c46410c6291200 0x006188c8218c5224 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z1063 : W := mkw 0xc968b05bf031a312 0xeb92d160b7e06346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z1064 : W := mkw 0x8128904b3010a110 0x2b02512096602142 0x81f8f8fe3031e3db 0xbb03f1f1fc6063c7

def z1065 : W := mkw 0x00482013ffff7fa5 0x0c00904027fffeff 0x00000001fffffffe 0x0c00000003ffffff

def z1066 : W := mkw 0xec9e00013d9c0004 0x87d93c00027b3800 0xfe3f0001fffe0061 0xeffc7e0003fffc00

def z1067 : W := mkw 0x061b0b8610d66d81 0x100c36170c21acdb 0x8e3f1f8e31fffffe 0x311c7e3f1c63ffff

def z1068 : W := mkw 0x6cde0001bdbc0004 0x8cd9bc00037b7800 0xfe3f0001fffe0061 0x6dfc7e0003fffc00

def z1069 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x80001801f031e3db 0x1900003003e063c7

def z1070 : W := mkw 0xca002a016b41d808 0x0794005402d683b0 0xfe001f01ffc1fc1d 0xdffc003e03ff83f8

def z1071 : W := mkw 0xedfe9001bdbc800c 0xcfdbfd20037b7900 0xffff0001fffe0061 0xeffffe0003fffc00

def z1072 : W := mkw 0x8168b05ad031a310 0x2b02d160b5a06346 0x81f8f8fe0031e3db 0xb303f1f1fc0063c7

def z1073 : W := mkw 0x8128b04b7011a100 0x2302516096e02342 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z1074 : W := mkw 0xf9e4f459ef29921c 0xeff3c9e8b3de5324 0x71c0e071ce000000 0x82e381c0e39c0000

def z1075 : W := mkw 0xda00de012b40d808 0x47b401bc025681b0 0xfe001f01ffc0fc0d 0xcffc003e03ff81f8

def z1076 : W := mkw 0xcf3a9a4f39d4e915 0xbf9e75349e73a9d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z1077 : W := mkw 0x6dfe00009dbc0004 0x8cdbfc00013b7800 0x7fff0001cffe0061 0xeefffe00039ffc00

def z1078 : W := mkw 0x24df018694be2581 0x1049be030d297c4b 0x01ff008e003e03e2 0x2003fe011c007c07

def z1079 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0x7fc70001fffe0060 0xceff8e0003fffc00

def z1080 : W := mkw 0x041a000010940000 0x0008340000212800 0xfe3f0001fffe0061 0xeffc7e0003fffc00

def z1081 : W := mkw 0x8168b05bf639b330 0x2b02d160b7ec7366 0x81f8f8fffe31e3db 0xbb03f1f1fffc63c7

def z1082 : W := mkw 0x20c4000084280000 0x0041880001085000 0xffc70001fffe0061 0xefff8e0003fffc00

def z1083 : W := mkw 0x8168b05bf439a310 0x2b02d160b7e87346 0x81f8f8fffe3fe3fb 0xbf03f1f1fffc7fc7

def z1084 : W := mkw 0xfdb7d5ec00000002 0xf3fb6fabd8000000 0xf1fff8fe00000001 0xb3e3fff1fc000000

def z1085 : W := mkw 0x00482012d6bf37a1 0x0000904025ad7e6f 0x00000001ce3f1ff6 0x0c000000039c7e3f

def z1086 : W := mkw 0xd920d44800000000 0x63b241a890000000 0xf1f8f8fe00000001 0xb3e3f1f1fc000000

def z1087 : W := mkw 0x7fb74fec00000002 0xf0ff6e9fd8000000 0x7fffe7fe00000001 0xf2ffffcffc000000

def z1088 : W := mkw 0x1321dfec00000002 0x702643bfd8000000 0x01f8fffe00000000 0x3003f1fffc000000

def z1089 : W := mkw 0xedb690480d8c0004 0xa7db6d20901b1800 0xfffff8fe0fce0021 0xf7fffff1fc1f9c00

def z1090 : W := mkw 0x37b74fec00000002 0xb06f6e9fd8000000 0xfffffffe00000001 0xf3fffffffc000000

def z1091 : W := mkw 0x06532b94c62b16a0 0x100ca657298c562d 0x8e3f1f8fce3f1ff7 0x7d1c7e3f1f9c7e3f

def z1092 : W := mkw 0xedf60001ad280000 0x87dbec00035a5000 0xffff0001fffe0061 0xeffffe0003fffc00

def z1093 : W := mkw 0x00482013f031a310 0x0800904027e06346 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z1094 : W := mkw 0xffb7dfec00000002 0xf3ff6fbfd8000000 0xfffffffe3001e019 0xfbfffffffc6003c0

def z1095 : W := mkw 0xc968b05bf031a310 0x2b92d160b7e06346 0xfff8f8fff031e3db 0xfbfff1f1ffe063c7

def z1096 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x01f8f8ffc031e3da 0xb203f1f1ff8063c7

def z1097 : W := mkw 0x7e974fa40bc65c8b 0xd4fd2e9f48178cb9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z1098 : W := mkw 0xa5fe0001b4bc0000 0x0b4bfc0003697800 0xffff0001fffe0061 0xeffffe0003fffc00

def z1099 : W := mkw 0x6cde00009dbc0004 0x84d9bc00013b7800 0xffff0001fffe0061 0xeffffe0003fffc00

def z1100 : W := mkw 0xffb7dfed2b40580a 0xf7ff6fbfda5680b0 0xffffffffffc01c05 0xffffffffffff8038

def z1101 : W := mkw 0x12016f8642437d81 0x102402df0c8486fb 0x0000ff8e0001ff9e 0x100001ff1c0003ff

def z1102 : W := mkw 0xdb20fe496b41d818 0x6fb641fc92d683b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z1103 : W := mkw 0x9733dfec00000002 0x732e67bfd8000000 0x8ffffffe00000001 0xf31ffffffc000000

def z1104 : W := mkw 0x00482012d0312300 0x0000904025a06246 0x00000001f031e3da 0x0800000003e063c7

def z1105 : W := mkw 0xf9e4f479ef299234 0xaff3c9e8f3de5324 0x71c0e071ce000000 0x82e381c0e39c0000

def z1106 : W := mkw 0xcb209a4800000000 0x6396413490000000 0x8ff8f8fe00000001 0xb31ff1f1fc000000

def z1107 : W := mkw 0x8120904800000000 0x2302412090000000 0x01f8e0fe00000000 0xa203f1c1fc000000

def z1108 : W := mkw 0x00482013ff7bffb8 0x0c00904027fef7ff 0x00000001fffffffe 0x0c00000003ffffff

def z1109 : W := mkw 0xffb6de6c00000002 0xf3ff6dbcd8000000 0xfff8f8fe00000001 0xb3fff1f1fc000000

def z1110 : W := mkw 0xa7b79bec00000002 0xb34f6f37d8000000 0x8ffffffe00000001 0xf31ffffffc000000

def z1111 : W := mkw 0xffb7dfec00840002 0xf3ff6fbfd8010800 0xfffffffe01ce0021 0xf7fffffffc039c00

def z1112 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81f8f8fff001e39a 0x9303f1f1ffe003c7

def z1113 : W := mkw 0xefb79bcc00000000 0xb3df6f3798000000 0xfffffffe00000001 0xf3fffffffc000000

def z1114 : W := mkw 0xca009a012940c808 0x4794013402528190 0xfe001f01ffc1fc1d 0xdffc003e03ff83f8

def z1115 : W := mkw 0xcf3a9a4f39d4e919 0x7f9e75349e73a9d2 0x8e38180e31c0e008 0x011c70301c6381c0

def z1116 : W := mkw 0x0168b05ad031a310 0x2802d160b5a06346 0x81f8f8fe3031e3db 0x3903f1f1fc6063c7

def z1117 : W := mkw 0xffb7dfec0f8e14a6 0xf7ff6fbfd81f1c29 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z1118 : W := mkw 0xa5b6904800000000 0xa34b6d2090000000 0x81fff8fe00000001 0xb303fff1fc000000

def z1119 : W := mkw 0x8128b05a5011a310 0x23025160b4a02346 0x81f8f8fe3031e3db 0xbb03f1f1fc6063c7

def z1120 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x81f8f8fff030e3ca 0xa303f1f1ffe061c7

def z1121 : W := mkw 0xffb7dfec09840006 0xf7ff6fbfd8130800 0xfffffffe01c00001 0xf3fffffffc038000

def z1122 : W := mkw 0xffb7dfec0f4a5caa 0xf7ff6fbfd81e94b9 0xfffffffe0fce1c25 0xf7fffffffc1f9c38

def z1123 : W := mkw 0x6cd600008dac0004 0x84d9ac00011b5800 0x7e070001cffe0060 0x4cfc0e00039ffc00

def z1124 : W := mkw 0x37b7dfec00000002 0xf06f6fbfd8000000 0x8ffffffe00000001 0x711ffffffc000000

def z1125 : W := mkw 0x041b018210962580 0x0008360304212c4b 0x8e3f1f8e31ffffff 0x7d1c7e3f1c63ffff

def z1126 : W := mkw 0x7e974fa40fce5ca5 0x94fd2e9f481f9cb9 0x7e0707000fce1c24 0x44fc0e0e001f9c38

def z1127 : W := mkw 0xffb7dfec0940480a 0xf7ff6fbfd8128090 0xfffffffe01c00001 0xf3fffffffc038000

def z1128 : W := mkw 0xdb20fe016b41d80c 0xcfb641fc02d683b0 0xfe00ff01ffc1fc1d 0xdffc01fe03ff83f8

def z1129 : W := mkw 0xfdb6d46800000002 0xe3fb6da8d0000000 0xfffff8fe00000001 0xf3fffff1fc000000

def z1130 : W := mkw 0x8160b05be021a310 0x2b02c160b7c04346 0x81f8f8ffc001e39b 0xb303f1f1ff8003c7

def z1131 : W := mkw 0x25b791ec00000002 0xb04b6f23d8000000 0x01fff8fe00000000 0x3003fff1fc000000

def z1132 : W := mkw 0x8168904bb0302100 0x2b02d12097606042 0x81f8f8fff031e3db 0xbb03f1f1ffe063c7

def z1133 : W := mkw 0xb1a5d5e8060a14a0 0x23634babd00c1429 0xf1fffffe0e0e1c25 0xf7e3fffffc1c1c38

def z1134 : W := mkw 0xedfe0001bdbc0004 0x8fdbfc00037b7800 0xffff0001ffce0020 0xc7fffe0003ff9c00

def z1135 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0xf1f8f8fffe31e3db 0xffe3f1f1fffc63c7

def z1136 : W := mkw 0xedfe9049bdbc0006 0xefdbfd20937b7800 0xffff0001fffe0061 0xeffffe0003fffc00

def z1137 : W := mkw 0xefb79bec00000002 0xf3df6f37d8000000 0x8ffff8fe00000001 0xb31ffff1fc000000

def z1138 : W := mkw 0x812191c800020480 0x2302432390000409 0x81fffffe003f1ff7 0xff03fffffc007e3f

def z1139 : W := mkw 0xffb7dfed29000006 0xffff6fbfda520000 0xfffffffe00000001 0xf3fffffffc000000

def z1140 : W := mkw 0x8120904920008010 0x2b02412092400100 0x81f8f8fe00000001 0xb303f1f1fc000000

def z1141 : W := mkw 0x30c545a0842a0480 0x00618a8b41085409 0x71c7e7f1ce3f1ff7 0xfee38fcfe39c7e3f

def z1142 : W := mkw 0x308545a000000000 0x00610a8b40000000 0xf1fffffe00000001 0xf3e3fffffc000000

def z1143 : W := mkw 0x25ff01de94be2795 0xb84bfe03bd297c4f 0x01ff00fe003e03e2 0x2003fe01fc007c07

def z1144 : W := mkw 0x83219bcc00000000 0x3306433798000000 0x81f8fffe00000001 0xb303f1fffc000000

def z1145 : W := mkw 0xe9a4904800000000 0xa3d3492090000000 0xf1f8f8fe00000001 0xb3e3f1f1fc000000

def z1146 : W := mkw 0xa1a4904800000000 0x2343492090000000 0xf1fff8fe00000001 0xf3e3fff1fc000000

def z1147 : W := mkw 0x8168b05bf031a310 0x2b02d160b7e06346 0x00000001f031e3da 0x0800000003e063c7

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z9,z3,z5,z8]),(0,[z1,z2,z3,z5,z10,z8,z6]),(0,[z11,z1,z12,z2,z3,z8,z6])],[(0,[z13,z1,z2,z14,z3,z5,z8]),(0,[z15,z1,z3,z16,z5,z8,z6]),(0,[z1,z2,z3,z17,z5,z8,z6]),(1,[z18,z1,z2,z3,z5,z8])],[(0,[z2,z3,z5,z8,z19,z6,z20])],[(0,[z21,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z22,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z23])],[(0,[z24,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z25,z8,z6]),(0,[z26,z2,z3,z5,z27,z8,z6]),(0,[z1,z2,z3,z5,z28,z8,z6]),(0,[z1,z2,z29,z3,z5,z8,z6]),(0,[z1,z2,z30,z5,z8,z6,z31])],[(0,[z32,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z33,z6]),(1,[z34,z2,z3,z5,z8,z20]),(0,[z1,z2,z3,z5,z8,z35,z6]),(0,[z1,z2,z36,z3,z37,z8,z6])],[(0,[z38,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z39,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z40,z6]),(0,[z1,z2,z3,z5,z8,z6,z41]),(1,[z42,z1,z2,z3,z5,z8]),(0,[z1,z43,z2,z3,z5,z8,z6]),(0,[z44,z1,z2,z3,z5,z8,z6])],[(1,[z1,z45,z2,z3,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z20]),(1,[z46,z2,z3,z5,z8,z19]),(0,[z1,z47,z2,z3,z5,z8,z6]),(0,[z48,z1,z2,z36,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z5,z8,z49,z6]),(0,[z1,z2,z3,z5,z50,z8,z51])],[(0,[z52,z1,z2,z14,z3,z5,z8]),(0,[z1,z2,z53,z3,z5,z8,z6]),(0,[z1,z2,z54,z3,z5,z8,z6]),(1,[z1,z2,z3,z55,z8,z6]),(0,[z1,z56,z2,z3,z5,z8,z6]),(0,[z1,z2,z57,z3,z5,z8,z6]),(0,[z1,z2,z36,z5,z37,z8,z6])],[(0,[z13,z1,z2,z58,z5,z8,z6]),(0,[z0,z1,z2,z14,z3,z5,z8]),(0,[z15,z1,z2,z14,z3,z5,z8]),(0,[z59,z42,z1,z2,z3,z5,z8]),(0,[z60,z1,z2,z3,z5,z8,z6])],[(0,[z61,z1,z2,z3,z62,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z63]),(0,[z1,z64,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z65,z8,z6]),(0,[z66,z1,z2,z14,z3,z5,z8])],[(0,[z67,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z68,z5,z8]),(0,[z1,z69,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z70,z5,z8,z6])],[(0,[z1,z71,z2,z3,z5,z8,z6]),(0,[z1,z72,z2,z14,z3,z5,z8]),(1,[z1,z2,z3,z73,z5,z8])],[(0,[z1,z2,z74,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z75,z6]),(1,[z1,z2,z76,z5,z8,z6]),(0,[z1,z2,z77,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z78,z5,z8,z6]),(0,[z46,z1,z79,z2,z3,z5,z8]),(0,[z1,z2,z80,z3,z5,z8,z6]),(0,[z1,z2,z81,z3,z5,z8,z6]),(0,[z82,z1,z2,z30,z5,z8,z6]),(1,[z11,z1,z12,z2,z3,z8])],[(1,[z1,z2,z3,z5,z8,z83]),(0,[z48,z1,z2,z14,z3,z5,z8]),(0,[z60,z1,z2,z4,z5,z8,z6])],[(0,[z13,z1,z2,z14,z5,z8,z6]),(0,[z1,z2,z14,z58,z3,z5,z8]),(0,[z26,z1,z2,z3,z5,z8,z84]),(0,[z85,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z86,z5,z8]),(0,[z87,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z88,z5,z8,z6])],[(0,[z32,z1,z89,z2,z5,z8,z6]),(1,[z0,z2,z3,z5,z90,z6]),(0,[z1,z2,z91,z3,z5,z8,z6]),(0,[z92,z1,z2,z3,z16,z5,z8])],[(1,[z1,z93,z2,z3,z5,z6]),(0,[z1,z94,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z95,z5,z8,z6]),(0,[z1,z2,z3,z5,z96,z37,z8]),(0,[z48,z1,z2,z5,z8,z97,z6]),(0,[z98,z42,z1,z2,z3,z5,z8]),(0,[z11,z1,z2,z3,z99,z8,z6]),(0,[z1,z100,z2,z3,z5,z8,z6])],[(0,[z101,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z97,z6]),(0,[z102,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z99,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z103,z6])],[(0,[z1,z2,z3,z5,z104,z8,z6]),(0,[z1,z2,z3,z105,z5,z8,z6]),(0,[z1,z2,z3,z106,z5,z8,z6]),(0,[z1,z2,z3,z107,z5,z8,z6])],[(0,[z1,z2,z108,z3,z5,z8,z6]),(0,[z109,z1,z2,z3,z5,z8,z6]),(0,[z110,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z111,z3,z5,z8,z6]),(0,[z44,z1,z2,z112,z3,z5,z6]),(0,[z1,z113,z2,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z5,z114,z8,z6]),(0,[z1,z2,z115,z3,z5,z8,z6])],[(0,[z1,z2,z3,z62,z5,z8,z6]),(0,[z116,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z117,z3,z5,z8,z6])],[(0,[z1,z2,z118,z119,z3,z5,z8]),(0,[z1,z120,z2,z3,z5,z8,z6]),(0,[z1,z121,z2,z3,z5,z8,z6]),(0,[z1,z56,z2,z112,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z122,z6]),(0,[z123,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z14,z3,z5,z8]),(0,[z42,z1,z124,z2,z3,z5,z8]),(0,[z42,z1,z2,z3,z5,z8,z125])],[(0,[z1,z2,z126,z3,z5,z8,z6]),(0,[z1,z127,z2,z3,z5,z8,z6])],[(0,[z128,z1,z2,z119,z5,z8,z6]),(0,[z129,z1,z2,z3,z5,z8,z6]),(0,[z130,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z131,z3,z5,z8,z6])],[(0,[z1,z2,z14,z5,z8,z97,z6])],[(0,[z42,z52,z1,z2,z3,z5,z8]),(0,[z132,z1,z133,z2,z3,z8,z6])],[(0,[z1,z134,z2,z3,z5,z8,z6]),(1,[z59,z1,z3,z86,z5,z8]),(0,[z11,z1,z2,z14,z3,z5,z8])]],
   [[(0,[z42,z26,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z135,z6]),(0,[z1,z2,z3,z5,z8,z136,z6]),(0,[z1,z2,z3,z137,z5,z8,z6]),(0,[z42,z1,z56,z2,z3,z5,z8])],[(0,[z26,z1,z2,z3,z5,z8,z6]),(0,[z1,z138,z139,z2,z3,z5,z6]),(0,[z1,z2,z14,z29,z3,z5,z8]),(1,[z1,z2,z3,z140,z8,z6]),(0,[z44,z1,z2,z3,z5,z50,z6])],[(0,[z1,z141,z2,z3,z5,z8,z6])],[(0,[z1,z2,z118,z3,z5,z8,z6]),(0,[z1,z2,z142,z3,z5,z8,z6]),(1,[z1,z89,z80,z5,z8,z6]),(0,[z143,z1,z2,z3,z5,z8,z6]),(0,[z1,z144,z2,z3,z5,z8,z6]),(0,[z42,z1,z12,z2,z3,z5,z8])],[(0,[z26,z1,z145,z2,z3,z8,z6]),(0,[z1,z133,z2,z3,z8,z146,z6]),(0,[z1,z2,z147,z3,z5,z8,z6]),(0,[z59,z1,z2,z3,z5,z8,z148])],[(0,[z1,z149,z2,z3,z5,z8,z6]),(0,[z150,z1,z2,z3,z5,z8,z6]),(0,[z151,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z2,z3,z5,z8,z6]),(0,[z44,z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z152,z8,z6])],[(0,[z1,z2,z119,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z153,z6]),(0,[z1,z154,z2,z3,z5,z8,z6]),(0,[z155,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z156,z8,z6]),(0,[z1,z157,z2,z3,z5,z8,z6])]],
   [[(1,[z1,z2,z3,z5,z8,z158]),(0,[z59,z1,z2,z3,z5,z8,z159]),(0,[z1,z160,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z161]),(0,[z1,z2,z14,z3,z5,z162,z6]),(0,[z42,z1,z139,z2,z3,z5,z8])],[(1,[z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z163]),(0,[z1,z2,z3,z164,z5,z8,z6])],[(1,[z26,z2,z3,z27,z8,z6]),(0,[z1,z2,z3,z5,z8,z165,z6]),(0,[z1,z2,z3,z5,z8,z6,z166]),(0,[z1,z167,z2,z3,z5,z8,z6]),(0,[z1,z2,z168,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z90,z6]),(0,[z1,z3,z169,z5,z8,z170,z6]),(0,[z1,z2,z3,z5,z8,z6,z171])],[(0,[z1,z2,z3,z5,z8,z172,z6]),(1,[z1,z138,z3,z169,z5,z6]),(0,[z42,z1,z2,z3,z5,z8,z159]),(0,[z1,z2,z3,z5,z173,z8,z6])],[(0,[z132,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z159]),(0,[z1,z174,z2,z3,z5,z8,z6]),(1,[z1,z2,z29,z5,z97,z6]),(0,[z1,z175,z2,z14,z3,z5,z8]),(0,[z67,z42,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z6,z176]),(0,[z1,z139,z2,z3,z5,z97,z6])],[(0,[z1,z2,z3,z177,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z178,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z179]),(0,[z1,z138,z2,z3,z5,z170,z6]),(0,[z1,z2,z3,z180,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z181]),(0,[z1,z2,z3,z5,z8,z6,z182]),(0,[z183,z1,z2,z14,z3,z5,z8]),(0,[z1,z2,z14,z3,z184,z5,z8])],[(0,[z26,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z185,z5,z8,z6]),(0,[z87,z42,z1,z2,z3,z5,z8])],[(0,[z186,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z72,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z187,z6])],[(0,[z188,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z189,z5,z8,z6]),(0,[z1,z2,z3,z190,z5,z8,z6]),(0,[z1,z2,z191,z3,z5,z8,z6]),(0,[z1,z145,z2,z3,z8,z6,z192])],[(0,[z1,z193,z2,z3,z5,z8,z6])],[(0,[z194,z1,z2,z3,z5,z8,z6]),(0,[z1,z195,z2,z3,z5,z8,z6]),(0,[z196,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z14,z5,z8,z31])],[(0,[z197,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z198,z3,z5,z8,z6]),(0,[z1,z199,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z200,z8,z6]),(0,[z201,z1,z139,z2,z3,z5,z6]),(0,[z1,z89,z2,z14,z3,z5,z8]),(0,[z1,z2,z202,z3,z5,z8,z6]),(0,[z1,z2,z36,z14,z3,z5,z8]),(0,[z1,z203,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z99,z5,z8])]],
   [[(0,[z1,z2,z3,z5,z8,z6,z204]),(0,[z42,z1,z2,z3,z5,z8,z19]),(0,[z1,z2,z205,z3,z5,z8,z6]),(0,[z82,z1,z2,z112,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z51])],[(0,[z1,z2,z3,z206,z5,z8,z6]),(0,[z1,z207,z2,z3,z5,z8,z6]),(0,[z208,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z209,z6]),(0,[z210,z1,z2,z3,z5,z8,z6]),(0,[z1,z89,z2,z3,z5,z8,z211])],[(0,[z46,z59,z1,z2,z3,z5,z8]),(0,[z212,z1,z2,z3,z5,z8,z6]),(0,[z1,z213,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z191,z3,z5,z8])],[(0,[z1,z2,z3,z5,z214,z8,z6]),(0,[z1,z2,z215,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z216,z8,z6]),(0,[z1,z2,z217,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z218]),(0,[z1,z2,z219,z14,z3,z5,z6]),(0,[z1,z2,z14,z5,z8,z6,z31])],[(0,[z220,z1,z2,z3,z5,z8,z6]),(0,[z32,z15,z1,z2,z5,z8,z6]),(0,[z0,z2,z3,z5,z8,z90,z6]),(0,[z1,z2,z3,z68,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z221]),(0,[z1,z2,z222,z14,z3,z5,z8]),(0,[z1,z223,z2,z14,z3,z5,z8])],[(0,[z42,z1,z2,z3,z224,z5,z8]),(0,[z34,z2,z3,z5,z8,z6,z20]),(0,[z1,z225,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z226,z8,z6])],[(0,[z1,z2,z3,z5,z8,z227,z6])],[(0,[z1,z2,z58,z3,z5,z8,z6]),(1,[z1,z228,z2,z3,z5,z6]),(0,[z1,z2,z3,z86,z5,z8,z19]),(0,[z1,z2,z3,z5,z8,z229,z6]),(0,[z1,z2,z3,z230,z5,z8,z6]),(0,[z231,z1,z2,z14,z3,z5,z8]),(0,[z232,z42,z1,z2,z3,z5,z8]),(0,[z233,z1,z2,z3,z5,z8,z6])]],
   [[(0,[z42,z1,z2,z3,z62,z5,z8]),(1,[z15,z1,z16,z5,z8,z6]),(0,[z1,z2,z3,z234,z5,z8,z6]),(0,[z1,z235,z2,z3,z5,z8,z6]),(0,[z1,z2,z236,z3,z5,z8,z6]),(0,[z1,z2,z237,z3,z5,z8,z6]),(0,[z1,z238,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z76,z5,z8,z6])],[(0,[z1,z1,z2,z3,z5,z8,z6]),(0,[z239,z2,z119,z3,z5,z8,z6]),(0,[z240,z1,z2,z119,z3,z5,z8]),(0,[z46,z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z241,z5,z8,z6]),(0,[z1,z12,z2,z3,z99,z5,z8])],[(0,[z0,z1,z56,z2,z3,z5,z6]),(0,[z42,z1,z2,z3,z5,z37,z8])],[(0,[z1,z242,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z243,z5,z8,z6]),(0,[z244,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z245,z6]),(0,[z1,z79,z2,z14,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z246,z6]),(0,[z1,z2,z3,z5,z8,z247,z6]),(0,[z1,z2,z3,z5,z248,z8,z6]),(0,[z1,z2,z3,z5,z8,z148,z51])],[(0,[z1,z249,z2,z3,z5,z8,z6])],[(1,[z32,z2,z62,z5,z8,z6]),(0,[z13,z2,z58,z3,z5,z8,z6]),(0,[z1,z2,z250,z3,z5,z8,z6]),(0,[z1,z251,z2,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z252,z3,z5,z8,z6]),(0,[z13,z1,z2,z3,z5,z8,z158]),(0,[z42,z1,z2,z3,z5,z27,z8]),(0,[z253,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z36,z3,z5,z8]),(1,[z48,z1,z2,z217,z8,z6]),(1,[z1,z2,z14,z3,z140,z8])],[(0,[z13,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z200,z8]),(1,[z42,z1,z2,z30,z5,z8])],[(0,[z1,z254,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z255,z5,z8,z6]),(0,[z240,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z256,z80,z3,z5,z6]),(0,[z257,z1,z2,z3,z5,z8,z6])],[(0,[z13,z1,z2,z62,z5,z8,z6]),(0,[z1,z258,z2,z3,z5,z8,z6]),(0,[z15,z1,z89,z3,z5,z8,z6]),(0,[z259,z1,z2,z3,z5,z8,z6]),(0,[z82,z1,z2,z3,z5,z97,z6]),(0,[z42,z1,z2,z3,z5,z50,z8]),(0,[z1,z2,z260,z3,z5,z8,z6]),(0,[z1,z2,z261,z3,z5,z8,z6]),(0,[z1,z2,z3,z262,z5,z8,z6])],[(1,[z1,z2,z3,z5,z173,z8])],[],[(0,[z1,z93,z2,z119,z3,z5,z6]),(0,[z1,z2,z263,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z169,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z264]),(0,[z1,z2,z3,z265,z5,z8,z6])],[(0,[z266,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z267,z5,z8,z6]),(0,[z59,z1,z79,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z268,z8,z6]),(0,[z1,z2,z3,z5,z8,z125,z6]),(0,[z1,z2,z3,z99,z5,z8,z148]),(0,[z1,z2,z269,z3,z5,z8,z6])]],
   [[(0,[z42,z1,z239,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z270,z8,z6]),(0,[z1,z271,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z8,z20]),(0,[z1,z2,z3,z5,z272,z8,z6]),(0,[z273,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z20]),(0,[z1,z274,z2,z3,z5,z8,z6]),(0,[z275,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z276,z5,z8,z6]),(0,[z59,z1,z2,z3,z86,z5,z8]),(0,[z1,z2,z14,z3,z3,z5,z8])],[(0,[z0,z1,z2,z3,z5,z8,z6]),(0,[z277,z1,z2,z3,z5,z8,z6]),(0,[z1,z278,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z4,z5,z8]),(0,[z42,z279,z1,z2,z3,z5,z8])],[(0,[z280,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z281,z8,z6]),(0,[z1,z2,z3,z5,z8,z20,z159]),(0,[z1,z56,z2,z3,z5,z170,z6]),(1,[z282,z1,z2,z3,z5,z8]),(0,[z18,z1,z2,z3,z5,z8,z6]),(0,[z283,z1,z2,z14,z3,z5,z8])],[(0,[z1,z2,z3,z5,z284,z8,z6]),(0,[z1,z285,z2,z3,z5,z8,z6]),(0,[z66,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z112,z3,z5,z8,z161])],[(0,[z26,z1,z133,z2,z3,z8,z6]),(0,[z1,z2,z3,z5,z8,z286,z6]),(0,[z1,z2,z112,z29,z3,z5,z6])],[(0,[z1,z72,z2,z3,z5,z8,z6]),(0,[z48,z1,z2,z217,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z192]),(0,[z1,z2,z3,z5,z140,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z287]),(0,[z1,z288,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z55,z8,z90,z6]),(0,[z1,z2,z3,z86,z5,z8,z20]),(0,[z1,z2,z3,z5,z8,z148,z20]),(0,[z1,z289,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z290,z5,z8,z6]),(0,[z1,z139,z145,z2,z3,z5,z6])]],
   [[(0,[z291,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z256,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z292,z8,z6]),(0,[z48,z1,z2,z3,z5,z8,z6]),(0,[z1,z293,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z50,z6,z51])],[(0,[z1,z2,z3,z5,z294,z8,z6]),(0,[z1,z239,z2,z14,z3,z5,z8]),(0,[z1,z2,z3,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z295,z6]),(0,[z1,z296,z2,z3,z5,z8,z6]),(0,[z297,z1,z2,z3,z5,z8,z6]),(0,[z298,z1,z2,z3,z5,z8,z6])],[(0,[z42,z1,z2,z58,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z299,z6])],[(0,[z2,z3,z224,z5,z27,z8,z6]),(0,[z1,z2,z3,z300,z5,z8,z6]),(0,[z1,z301,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z241,z5,z8]),(0,[z1,z2,z3,z5,z173,z8,z97])],[(1,[z1,z2,z302,z5,z8,z6]),(0,[z1,z2,z3,z303,z5,z8,z6]),(0,[z1,z138,z2,z3,z5,z97,z6]),(1,[z1,z2,z36,z37,z8,z6]),(0,[z1,z2,z5,z37,z8,z97,z6])],[(0,[z1,z2,z3,z5,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z304]),(1,[z1,z56,z3,z5,z170,z6]),(0,[z82,z1,z2,z5,z37,z8,z6])],[(0,[z32,z1,z2,z3,z5,z305,z6]),(0,[z1,z2,z3,z5,z306,z8,z6])]],
   [[],[(0,[z1,z2,z307,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z308]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z1,z2,z3,z5,z309,z8,z6])],[(0,[z1,z2,z3,z5,z8,z83,z6]),(0,[z232,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z310,z3,z5,z8,z6]),(0,[z59,z1,z12,z2,z3,z5,z8]),(1,[z1,z2,z3,z5,z8,z161]),(0,[z1,z2,z14,z3,z5,z8,z6])],[(0,[z1,z89,z2,z3,z68,z5,z8]),(0,[z42,z1,z2,z14,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z192]),(0,[z1,z2,z3,z311,z5,z8,z6])],[(0,[z46,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z8,z166]),(0,[z1,z2,z3,z5,z8,z162,z6])],[(0,[z1,z2,z3,z5,z8,z6,z312]),(0,[z1,z2,z112,z3,z5,z90,z6]),(0,[z1,z2,z3,z5,z8,z6,z313])],[(0,[z1,z314,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z315,z5,z8,z6]),(0,[z1,z2,z3,z316,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z317,z6]),(0,[z48,z1,z2,z217,z3,z8,z6]),(0,[z318,z1,z2,z3,z5,z8,z6])],[(0,[z11,z1,z2,z3,z5,z8,z6])]],
   [[(0,[z1,z319,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z320]),(0,[z1,z2,z3,z321,z5,z8,z6]),(0,[z1,z223,z2,z3,z5,z6,z51])],[(0,[z1,z2,z3,z322,z5,z8,z6]),(0,[z1,z89,z80,z3,z5,z8,z6])],[(0,[z42,z1,z2,z29,z3,z5,z8])],[(0,[z1,z323,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z324,z6]),(0,[z282,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z325]),(0,[z1,z326,z2,z3,z5,z8,z6]),(0,[z327,z1,z2,z3,z5,z8,z6])],[(0,[z328,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z329]),(0,[z1,z2,z330,z3,z5,z8,z6])],[(0,[z26,z132,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z331,z8,z6]),(0,[z1,z332,z2,z3,z5,z8,z6]),(0,[z1,z2,z333,z3,z5,z8,z6]),(1,[z1,z2,z22,z14,z3,z8]),(0,[z1,z2,z30,z3,z5,z8,z6])],[(0,[z1,z334,z2,z3,z5,z8,z6]),(1,[z1,z72,z3,z8,z146,z6]),(0,[z1,z2,z3,z5,z8,z6,z335]),(0,[z1,z2,z336,z3,z5,z8,z6]),(0,[z1,z2,z3,z337,z5,z8,z6]),(0,[z1,z2,z338,z14,z3,z5,z8]),(0,[z1,z139,z2,z14,z3,z5,z8])]],
   [[(0,[z1,z2,z3,z5,z97,z90,z6]),(0,[z1,z2,z339,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z19,z6]),(0,[z1,z2,z3,z5,z8,z340,z6]),(0,[z1,z2,z3,z341,z5,z8,z6]),(0,[z1,z2,z342,z3,z5,z8,z6])],[(0,[z32,z13,z2,z3,z5,z8,z6]),(0,[z1,z343,z2,z3,z5,z8,z6]),(0,[z1,z72,z2,z3,z241,z8,z6]),(0,[z1,z3,z241,z5,z8,z146,z6]),(1,[z1,z2,z344,z5,z8,z6])],[(0,[z345,z1,z2,z14,z3,z5,z8]),(0,[z346,z1,z2,z3,z5,z8,z6]),(0,[z15,z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z347,z5,z8,z6])],[(0,[z348,z1,z2,z3,z5,z8,z6]),(0,[z349,z1,z2,z3,z5,z8,z6])],[(0,[z350,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z300,z5,z27,z6]),(0,[z11,z1,z2,z217,z3,z8,z6]),(0,[z42,z1,z2,z14,z5,z8,z6])],[(0,[z1,z351,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z352,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z353]),(0,[z1,z2,z3,z5,z8,z6,z354]),(0,[z355,z1,z2,z3,z5,z8,z6]),(0,[z1,z175,z2,z3,z5,z8,z6]),(0,[z1,z356,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z50,z8,z6])],[(0,[z61,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z357,z5,z8,z6]),(0,[z59,z1,z3,z86,z5,z8,z6]),(0,[z358,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z14,z3,z5,z8,z90]),(0,[z34,z1,z2,z3,z5,z8,z19]),(0,[z1,z359,z2,z3,z5,z8,z6]),(0,[z1,z2,z360,z14,z3,z5,z8])]],
   [[(0,[z1,z2,z3,z5,z8,z361,z6]),(0,[z362,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z22,z14,z3,z5,z8]),(0,[z363,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z364,z6]),(0,[z44,z1,z223,z2,z3,z5,z6])],[(0,[z345,z52,z2,z3,z5,z8,z6]),(1,[z345,z119,z3,z5,z8,z6]),(0,[z183,z1,z2,z3,z5,z8,z6]),(0,[z48,z1,z2,z3,z5,z40,z6]),(0,[z1,z2,z3,z5,z8,z365,z6])],[(0,[z32,z1,z2,z14,z3,z5,z8]),(0,[z366,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z367,z6]),(0,[z1,z80,z3,z16,z5,z8,z6]),(0,[z368,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z369,z5,z8]),(0,[z297,z42,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z370,z5,z8,z6]),(0,[z42,z1,z133,z2,z3,z5,z8]),(0,[z1,z2,z3,z371,z5,z8,z6]),(0,[z1,z2,z3,z37,z8,z6,z148]),(1,[z1,z2,z3,z5,z187,z6]),(0,[z1,z2,z29,z3,z5,z97,z6]),(0,[z44,z1,z2,z330,z5,z8,z6])],[(0,[z1,z2,z372,z3,z5,z8,z6]),(0,[z1,z2,z373,z3,z5,z8,z6]),(0,[z1,z2,z3,z241,z5,z8,z166]),(0,[z374,z1,z2,z3,z5,z8,z6])],[(0,[z1,z375,z2,z3,z5,z8,z6]),(0,[z376,z1,z2,z3,z5,z8,z6]),(0,[z377,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z300,z5,z6]),(0,[z1,z2,z3,z378,z5,z8,z6]),(0,[z1,z2,z379,z3,z5,z8,z6]),(0,[z1,z2,z3,z380,z5,z8,z6]),(0,[z44,z1,z2,z3,z5,z97,z6]),(0,[z1,z2,z219,z14,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z381,z6]),(0,[z382,z1,z2,z3,z5,z8,z6]),(0,[z383,z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z384])],[(0,[z1,z89,z2,z3,z5,z8,z6]),(0,[z1,z2,z36,z3,z5,z8,z6])]],
   [[(0,[z385,z1,z2,z3,z5,z8,z6]),(0,[z1,z56,z2,z3,z5,z97,z6]),(0,[z1,z2,z3,z5,z8,z386,z6]),(1,[z1,z2,z3,z5,z8,z23]),(0,[z1,z387,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z158,z6]),(0,[z1,z2,z3,z5,z8,z6,z388]),(0,[z389,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z8,z51])],[(0,[z1,z2,z3,z5,z8,z6,z390]),(0,[z32,z1,z2,z3,z5,z25,z6]),(0,[z1,z2,z3,z391,z5,z8,z6]),(1,[z1,z2,z256,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z392,z6]),(0,[z1,z2,z393,z3,z5,z8,z6]),(0,[z1,z394,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z51])],[(1,[z1,z2,z3,z5,z305,z6]),(0,[z1,z2,z395,z3,z5,z8,z6]),(0,[z1,z396,z2,z3,z5,z8,z6]),(0,[z18,z1,z2,z3,z5,z8,z97])],[(0,[z397,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z398,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z146]),(0,[z1,z223,z2,z3,z5,z8,z6])],[(0,[z13,z1,z2,z30,z5,z8,z6]),(0,[z1,z12,z2,z3,z5,z8,z19]),(0,[z1,z2,z399,z3,z5,z8,z6]),(0,[z1,z400,z2,z3,z5,z8,z6]),(0,[z1,z401,z2,z3,z5,z8,z6])],[(0,[z402,z1,z2,z3,z5,z8,z6]),(0,[z403,z1,z2,z3,z5,z8,z6]),(0,[z404,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z112,z3,z4,z5,z6])],[(0,[z1,z405,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z406,z6]),(0,[z231,z1,z2,z3,z5,z8,z6]),(0,[z11,z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z407,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z408,z5,z8,z6]),(0,[z1,z2,z3,z5,z409,z8,z6])],[(0,[z201,z1,z2,z3,z5,z90,z6]),(0,[z1,z2,z3,z410,z5,z8,z6])],[(0,[z1,z2,z411,z3,z5,z8,z6])],[(0,[z1,z2,z3,z412,z5,z8,z6]),(0,[z1,z12,z2,z3,z5,z8,z51])],[(0,[z413,z1,z2,z3,z5,z8,z6]),(0,[z1,z79,z2,z3,z5,z8,z6]),(0,[z1,z2,z414,z3,z5,z8,z6]),(0,[z1,z2,z217,z3,z369,z5,z8]),(0,[z82,z1,z2,z14,z3,z5,z8])],[(0,[z0,z1,z139,z2,z3,z5,z6]),(0,[z1,z2,z3,z415,z5,z8,z6]),(0,[z416,z1,z2,z14,z3,z5,z8]),(0,[z1,z2,z3,z184,z5,z8,z6]),(0,[z42,z1,z145,z2,z3,z5,z8]),(0,[z417,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z418,z6]),(0,[z1,z2,z3,z5,z419,z8,z6]),(0,[z1,z2,z3,z5,z8,z420,z6]),(0,[z1,z242,z2,z3,z5,z146,z6]),(0,[z42,z1,z138,z2,z3,z5,z8]),(0,[z42,z1,z421,z2,z3,z5,z8]),(0,[z1,z2,z422,z3,z5,z8,z6]),(0,[z423,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z424,z5,z8,z6]),(0,[z34,z1,z2,z3,z5,z8,z20]),(0,[z1,z2,z425,z3,z5,z8,z6]),(0,[z1,z2,z3,z426,z5,z8,z6]),(0,[z1,z427,z2,z3,z5,z8,z6]),(0,[z1,z2,z428,z3,z5,z8,z6])]],
   [[(0,[z345,z1,z2,z3,z5,z8,z390]),(0,[z1,z138,z2,z3,z169,z5,z6]),(0,[z1,z2,z429,z3,z5,z8,z6]),(0,[z1,z2,z112,z14,z3,z5,z8]),(0,[z1,z2,z3,z430,z5,z8,z6]),(0,[z1,z2,z3,z5,z431,z8,z6])],[],[(0,[z1,z432,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z16,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z97]),(0,[z1,z124,z2,z3,z5,z8,z6]),(0,[z1,z433,z2,z3,z5,z8,z6]),(0,[z1,z2,z434,z3,z5,z8,z6])],[(0,[z132,z1,z72,z2,z3,z8,z6]),(0,[z2,z3,z5,z200,z8,z90,z6]),(0,[z46,z2,z3,z5,z8,z19,z6]),(0,[z1,z79,z3,z5,z8,z6,z159]),(0,[z1,z2,z112,z5,z8,z97,z6])],[(0,[z52,z1,z2,z3,z5,z8,z6]),(0,[z1,z133,z2,z14,z3,z5,z8]),(0,[z1,z138,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z435,z5,z8,z6]),(0,[z436,z1,z2,z3,z5,z8,z6])],[(0,[z52,z1,z119,z3,z5,z8,z6]),(0,[z1,z375,z2,z119,z3,z8,z6]),(0,[z15,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z80,z3,z5,z8]),(0,[z1,z2,z3,z4,z5,z97,z6]),(0,[z1,z2,z437,z3,z5,z8,z6])],[(0,[z438,z1,z2,z3,z5,z8,z6]),(0,[z1,z439,z2,z3,z5,z8,z6]),(0,[z440,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z441,z6])],[(0,[z442,z1,z2,z3,z5,z8,z6]),(0,[z1,z228,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z169,z5,z8]),(0,[z42,z1,z2,z217,z3,z5,z8]),(0,[z443,z1,z2,z3,z5,z8,z6]),(0,[z1,z444,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z445,z5,z8,z6])]],
   [[(0,[z42,z1,z2,z3,z5,z446,z8])],[(0,[z1,z93,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z447,z6]),(0,[z1,z2,z3,z5,z8,z448,z6]),(0,[z449,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z450,z6]),(0,[z1,z2,z3,z451,z5,z8,z6]),(0,[z452,z1,z2,z3,z5,z8,z6]),(0,[z44,z1,z2,z3,z5,z8,z51])],[(0,[z13,z1,z89,z2,z5,z8,z6]),(0,[z42,z1,z79,z2,z3,z5,z8]),(0,[z42,z1,z2,z3,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z453,z6]),(0,[z46,z34,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z4,z5,z8]),(0,[z1,z454,z2,z3,z5,z8,z6])],[(0,[z201,z0,z2,z3,z5,z8,z6]),(0,[z455,z1,z2,z3,z5,z8,z6]),(0,[z1,z72,z133,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z148]),(0,[z1,z2,z3,z456,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z84]),(0,[z132,z1,z2,z3,z224,z8,z6]),(0,[z201,z1,z138,z2,z3,z5,z6]),(0,[z1,z12,z2,z3,z5,z8,z20]),(1,[z1,z2,z3,z5,z457,z6]),(0,[z82,z1,z2,z14,z5,z8,z6]),(0,[z1,z2,z14,z3,z140,z8,z6]),(0,[z1,z2,z3,z5,z8,z458,z6]),(0,[z459,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z460,z8,z6])],[(0,[z1,z2,z461,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z8,z6]),(0,[z1,z462,z2,z3,z5,z8,z6]),(0,[z463,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z464,z16,z5,z8]),(0,[z465,z1,z2,z3,z5,z8,z6]),(0,[z1,z72,z2,z3,z8,z146,z6]),(0,[z1,z138,z2,z14,z3,z5,z8]),(0,[z1,z2,z3,z73,z5,z8,z6]),(1,[z1,z2,z330,z5,z8,z6])],[(0,[z1,z45,z2,z3,z8,z90,z6]),(0,[z1,z2,z3,z464,z5,z8,z6]),(0,[z1,z2,z3,z5,z466,z8,z6]),(0,[z1,z2,z3,z5,z8,z467,z6]),(0,[z42,z1,z2,z3,z5,z8,z192]),(0,[z1,z2,z3,z5,z8,z468,z6])]],
   [[(0,[z469,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z470,z5,z8,z6]),(0,[z1,z2,z3,z5,z471,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z159]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z8,z6,z192]),(0,[z472,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z473,z6])],[(0,[z201,z1,z2,z3,z5,z200,z6]),(0,[z474,z1,z2,z3,z5,z8,z6]),(0,[z383,z1,z2,z3,z5,z8,z6]),(0,[z11,z1,z2,z3,z5,z8,z148]),(0,[z1,z2,z3,z5,z8,z475,z6])],[(0,[z1,z239,z2,z3,z5,z8,z6]),(0,[z132,z1,z2,z14,z3,z5,z8]),(0,[z34,z1,z2,z14,z3,z5,z8]),(0,[z1,z2,z476,z3,z5,z8,z6]),(0,[z59,z1,z2,z14,z3,z5,z8]),(1,[z1,z2,z14,z3,z5,z162]),(1,[z1,z2,z219,z14,z3,z5]),(0,[z42,z1,z223,z2,z3,z5,z8]),(0,[z1,z2,z3,z344,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z477]),(0,[z1,z2,z3,z5,z457,z8,z6]),(0,[z42,z48,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z4,z8,z6,z192])],[(0,[z478,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z16,z5,z8]),(0,[z1,z2,z14,z3,z5,z8,z170]),(0,[z1,z12,z79,z2,z3,z5,z8]),(0,[z82,z1,z2,z29,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z479,z6])],[(1,[z1,z2,z118,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z480,z6]),(0,[z42,z1,z2,z3,z5,z481,z8])],[(1,[z1,z2,z3,z5,z25,z6]),(1,[z1,z2,z3,z5,z8,z163]),(0,[z1,z2,z3,z5,z8,z146,z6]),(0,[z1,z482,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z31]),(0,[z1,z2,z4,z344,z5,z8,z6])],[(0,[z1,z139,z56,z2,z3,z5,z6]),(0,[z1,z3,z86,z5,z8,z6,z159])]],
   [[(0,[z483,z1,z2,z3,z5,z8,z6]),(1,[z42,z1,z2,z14,z5,z8]),(0,[z1,z2,z14,z3,z5,z8,z162])],[(0,[z1,z484,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z485,z6]),(0,[z1,z2,z3,z5,z8,z6,z211]),(0,[z1,z2,z9,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z486,z8,z6]),(0,[z1,z487,z2,z3,z5,z8,z6])],[(0,[z201,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z8,z19,z148]),(1,[z92,z1,z2,z3,z5,z8]),(0,[z488,z1,z2,z3,z5,z8,z6]),(0,[z1,z489,z2,z3,z5,z8,z6]),(0,[z1,z145,z2,z14,z3,z5,z8])],[(0,[z1,z2,z490,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z491]),(0,[z1,z2,z3,z5,z457,z146,z6]),(0,[z42,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z99,z5,z8])],[(0,[z1,z2,z3,z5,z8,z492,z6]),(0,[z42,z132,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z6]),(1,[z1,z2,z3,z5,z96,z8]),(0,[z1,z2,z493,z3,z5,z8,z6])],[],[(0,[z1,z2,z3,z5,z8,z494,z6]),(0,[z1,z495,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z200,z97,z6]),(0,[z46,z1,z2,z3,z5,z8,z19]),(0,[z1,z2,z3,z5,z8,z19,z159]),(1,[z1,z2,z3,z5,z8,z182])],[(0,[z52,z1,z239,z3,z5,z8,z6]),(0,[z1,z228,z2,z3,z5,z27,z6]),(0,[z132,z2,z3,z224,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z496]),(0,[z1,z2,z497,z3,z5,z8,z6])]],
   [[(0,[z132,z1,z2,z3,z27,z8,z6]),(0,[z498,z1,z2,z3,z5,z8,z6]),(0,[z1,z79,z2,z3,z86,z5,z8]),(0,[z1,z12,z2,z14,z3,z5,z8]),(0,[z1,z499,z2,z3,z5,z8,z6])],[(0,[z500,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z224,z5,z8])],[(0,[z1,z2,z501,z3,z5,z8,z6]),(0,[z1,z502,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z503,z6]),(0,[z1,z2,z3,z86,z5,z8,z6]),(0,[z1,z504,z2,z3,z5,z8,z6])],[(0,[z1,z56,z2,z3,z169,z5,z6]),(0,[z1,z505,z2,z3,z5,z8,z6]),(0,[z1,z2,z506,z3,z5,z8,z6])],[(0,[z201,z1,z2,z14,z3,z5,z8]),(0,[z1,z507,z2,z3,z5,z8,z6]),(0,[z508,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z509,z5,z8,z6]),(0,[z1,z2,z3,z5,z510,z8,z6]),(0,[z1,z2,z3,z5,z8,z511,z6])],[(0,[z512,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z22,z3,z8,z6]),(0,[z279,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z513,z5,z8,z6,z20]),(0,[z1,z2,z80,z3,z5,z245,z6]),(0,[z514,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z515,z5,z8,z6]),(0,[z1,z2,z217,z36,z3,z8,z6]),(0,[z1,z2,z14,z3,z5,z37,z8]),(0,[z516,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z517,z3,z5,z8,z6])],[(0,[z1,z2,z3,z518,z5,z8,z6]),(0,[z1,z2,z519,z3,z5,z8,z6]),(0,[z1,z520,z2,z3,z5,z8,z6]),(0,[z521,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z522,z8,z6]),(0,[z1,z89,z2,z16,z5,z8,z6]),(0,[z1,z56,z2,z3,z4,z5,z6]),(0,[z1,z2,z523,z3,z5,z8,z6]),(0,[z1,z2,z338,z3,z5,z8,z6]),(0,[z1,z524,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z525,z5,z8,z6]),(0,[z1,z139,z2,z3,z5,z8,z6])]],
   [[(0,[z526,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z4,z5,z8,z23]),(0,[z1,z2,z527,z3,z5,z8,z6])],[(0,[z1,z528,z2,z3,z5,z8,z6]),(0,[z1,z2,z529,z3,z5,z8,z6]),(0,[z449,z42,z1,z2,z3,z5,z8]),(0,[z1,z139,z2,z3,z5,z6,z192]),(0,[z1,z223,z12,z2,z3,z5,z8])],[(0,[z345,z1,z2,z3,z5,z8,z6]),(1,[z128,z1,z2,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z530,z6]),(0,[z1,z2,z3,z531,z5,z8,z6]),(0,[z532,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z533,z8,z6]),(0,[z42,z1,z2,z3,z456,z5,z8]),(0,[z1,z139,z145,z2,z3,z8,z6]),(0,[z44,z1,z223,z2,z3,z5,z8])],[(0,[z1,z2,z534,z3,z5,z8,z6]),(0,[z1,z2,z3,z322,z62,z5,z8]),(1,[z82,z1,z2,z14,z5,z8])],[(1,[z1,z2,z3,z5,z8,z390]),(0,[z1,z2,z3,z535,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z27,z8]),(0,[z1,z536,z2,z3,z5,z8,z6]),(0,[z537,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z112,z3,z5,z6,z51]),(1,[z1,z139,z145,z2,z3,z6]),(0,[z1,z538,z2,z3,z5,z8,z6])],[(0,[z1,z539,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z540,z8,z6]),(0,[z1,z541,z2,z3,z5,z8,z6]),(0,[z542,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z112,z3,z73,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z543])],[(0,[z1,z2,z3,z5,z8,z6,z544]),(0,[z1,z2,z545,z3,z5,z8,z6]),(0,[z1,z2,z3,z546,z5,z8,z6]),(0,[z1,z2,z3,z547,z5,z8,z6]),(0,[z548,z1,z2,z3,z5,z8,z6]),(0,[z44,z1,z2,z14,z3,z5,z8]),(0,[z1,z223,z2,z3,z5,z8,z148])],[(0,[z1,z2,z513,z3,z5,z8,z6]),(0,[z1,z2,z360,z3,z5,z8,z6]),(0,[z1,z2,z3,z549,z5,z8,z6]),(0,[z1,z2,z29,z5,z8,z97,z6]),(0,[z1,z2,z14,z3,z5,z50,z8]),(0,[z1,z2,z3,z550,z5,z8,z6]),(0,[z1,z2,z3,z551,z5,z8,z6])]],
   [[(0,[z552,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z553,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z8,z90]),(0,[z1,z2,z112,z3,z5,z200,z6]),(0,[z1,z2,z3,z5,z8,z554,z6]),(0,[z1,z2,z3,z5,z96,z8,z6]),(0,[z282,z1,z2,z3,z5,z37,z8]),(0,[z1,z2,z217,z3,z5,z8,z182]),(0,[z1,z555,z2,z3,z5,z8,z6])],[(0,[z1,z314,z2,z119,z3,z8,z6]),(0,[z556,z1,z2,z3,z5,z8,z6]),(0,[z1,z56,z2,z14,z3,z5,z8]),(0,[z1,z557,z2,z3,z5,z8,z6])],[(1,[z61,z1,z2,z3,z5,z8]),(0,[z1,z2,z558,z3,z5,z8,z6]),(0,[z559,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z560,z8,z6])],[(0,[z1,z2,z534,z119,z5,z8,z6]),(0,[z1,z2,z3,z224,z5,z8,z6]),(0,[z561,z1,z2,z3,z5,z8,z6]),(0,[z1,z89,z2,z80,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z562,z6]),(0,[z1,z2,z217,z3,z8,z6,z148]),(0,[z1,z12,z2,z3,z8,z6,z148])],[(0,[z32,z1,z2,z62,z5,z8,z6]),(0,[z563,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z564,z8,z6])],[(1,[z1,z314,z2,z3,z8,z6]),(0,[z1,z2,z217,z5,z37,z8,z6]),(0,[z67,z1,z2,z14,z3,z5,z8]),(1,[z1,z2,z219,z3,z5,z6]),(0,[z1,z2,z219,z3,z5,z8,z6])],[(0,[z32,z1,z2,z58,z5,z8,z6]),(0,[z13,z1,z2,z3,z5,z8,z163]),(0,[z15,z13,z1,z2,z5,z8,z6]),(0,[z46,z1,z2,z3,z5,z8,z20]),(0,[z1,z2,z565,z3,z5,z8,z6]),(0,[z1,z79,z2,z3,z5,z8,z148]),(0,[z566,z42,z1,z2,z3,z5,z8])],[(0,[z1,z2,z222,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z97,z6,z51])]],
   [[(0,[z1,z2,z3,z567,z5,z8,z6]),(0,[z568,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z569,z3,z5,z8,z6]),(0,[z570,z1,z2,z3,z5,z8,z6]),(0,[z1,z139,z2,z112,z3,z5,z6]),(0,[z1,z139,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z5,z571,z8,z6]),(0,[z572,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z573,z5,z8,z6]),(0,[z1,z574,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z86,z5,z8])],[(0,[z26,z1,z72,z2,z3,z8,z6]),(0,[z575,z1,z2,z3,z5,z8,z6]),(0,[z1,z79,z2,z3,z5,z8,z159])],[(0,[z1,z2,z3,z576,z5,z8,z6]),(0,[z42,z13,z1,z2,z3,z5,z8]),(0,[z1,z56,z3,z5,z8,z170,z6]),(0,[z42,z42,z1,z2,z3,z5,z8])],[(1,[z1,z79,z3,z5,z8,z159])],[(0,[z577,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z55,z5,z8,z6]),(0,[z42,z201,z1,z2,z3,z5,z8]),(0,[z1,z578,z2,z3,z5,z8,z6]),(0,[z15,z1,z2,z16,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z8,z146]),(1,[z1,z133,z3,z241,z8,z6]),(1,[z1,z2,z3,z99,z8,z148])],[(0,[z579,z1,z2,z3,z5,z8,z6]),(0,[z32,z1,z2,z14,z5,z8,z6]),(0,[z1,z2,z580,z3,z5,z8,z6]),(0,[z1,z2,z3,z581,z5,z8,z6]),(0,[z582,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z481,z8,z6])],[(1,[z1,z2,z3,z5,z245,z6]),(0,[z1,z583,z2,z3,z5,z8,z6]),(0,[z1,z2,z111,z14,z3,z5,z8])]],
   [[(1,[z1,z254,z2,z3,z5,z6]),(0,[z584,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z585]),(0,[z1,z2,z3,z5,z8,z586,z6]),(0,[z1,z2,z587,z3,z5,z8,z6])],[(0,[z128,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z588,z8,z6]),(0,[z1,z2,z589,z3,z5,z8,z6]),(0,[z1,z2,z3,z590,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z591,z6]),(0,[z92,z1,z2,z3,z5,z8,z6]),(0,[z1,z138,z56,z3,z5,z8,z6]),(0,[z1,z2,z3,z592,z5,z8,z6]),(0,[z593,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z594,z6]),(0,[z595,z1,z2,z3,z5,z8,z6])],[(0,[z1,z45,z2,z3,z5,z8,z6]),(0,[z1,z2,z596,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z597]),(0,[z1,z2,z3,z5,z8,z598,z6])],[(0,[z1,z2,z3,z599,z5,z8,z6]),(0,[z1,z2,z600,z3,z5,z8,z6])],[(0,[z601,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z602]),(0,[z26,z1,z2,z3,z224,z8,z6]),(0,[z1,z2,z3,z5,z8,z603,z6]),(0,[z82,z1,z2,z3,z5,z8,z6]),(0,[z604,z1,z2,z3,z5,z8,z6]),(0,[z605,z1,z2,z3,z5,z8,z6])],[(0,[z345,z1,z239,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z200,z8]),(0,[z59,z34,z1,z2,z3,z5,z8]),(0,[z416,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z606,z5,z8,z6])],[(0,[z1,z2,z3,z5,z607,z8,z6]),(0,[z1,z2,z608,z3,z5,z8,z6]),(0,[z1,z72,z3,z5,z8,z146,z6]),(0,[z1,z2,z3,z609,z5,z8,z6]),(0,[z1,z2,z3,z610,z5,z8,z6]),(0,[z1,z611,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z30,z3,z5,z8])],[(1,[z1,z2,z3,z5,z8,z84]),(0,[z612,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z613,z8,z6]),(0,[z614,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z464,z5,z8]),(0,[z1,z2,z3,z5,z8,z615,z6]),(1,[z1,z2,z3,z5,z50,z51])]],
   [[(0,[z616,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z617]),(0,[z1,z2,z112,z3,z5,z8,z6]),(0,[z1,z618,z2,z3,z5,z8,z6])],[(0,[z619,z1,z2,z3,z5,z8,z6]),(0,[z26,z1,z2,z14,z3,z5,z8]),(0,[z34,z1,z79,z2,z3,z5,z8]),(0,[z42,z34,z1,z2,z3,z5,z8]),(0,[z1,z2,z302,z5,z8,z6,z20]),(0,[z46,z1,z2,z14,z3,z5,z8]),(0,[z15,z1,z2,z80,z5,z8,z6]),(0,[z620,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z621]),(0,[z1,z2,z3,z5,z8,z622,z6])],[(0,[z345,z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z623,z3,z5,z8,z6]),(0,[z624,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z625,z3,z5,z8,z6])],[(0,[z626,z1,z2,z3,z5,z8,z6]),(0,[z2,z58,z3,z62,z5,z8,z6]),(0,[z26,z1,z2,z3,z5,z8,z627]),(0,[z1,z628,z2,z3,z5,z8,z6]),(0,[z1,z629,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z8,z97]),(0,[z1,z2,z630,z3,z5,z8,z6])],[(0,[z1,z133,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z631]),(1,[z82,z1,z2,z112,z5,z6]),(0,[z1,z2,z22,z14,z3,z8,z6]),(0,[z1,z2,z3,z632,z5,z8,z6])],[(0,[z32,z2,z3,z62,z5,z8,z6]),(0,[z1,z2,z3,z5,z633,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z634]),(0,[z1,z2,z635,z3,z5,z8,z6]),(0,[z82,z48,z1,z2,z5,z8,z6])],[(1,[z32,z1,z2,z14,z5,z8]),(1,[z1,z2,z513,z5,z8,z6]),(0,[z283,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z80,z3,z5,z8]),(0,[z636,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z637,z6])],[(0,[z1,z2,z119,z14,z3,z5,z8]),(0,[z0,z1,z2,z3,z5,z90,z6]),(0,[z1,z2,z3,z638,z5,z8,z6]),(0,[z1,z2,z3,z639,z5,z8,z6]),(0,[z48,z1,z2,z3,z37,z8,z6]),(1,[z1,z2,z14,z5,z8,z97]),(0,[z11,z1,z12,z2,z3,z5,z8])]],
   [[(0,[z1,z640,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z99,z8,z6,z148])],[(0,[z1,z2,z3,z5,z27,z8,z6]),(0,[z641,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z14,z3,z5,z8]),(0,[z1,z2,z3,z642,z5,z8,z6]),(0,[z1,z643,z2,z3,z5,z8,z6]),(0,[z1,z223,z2,z3,z5,z50,z8]),(0,[z1,z2,z644,z3,z5,z8,z6])],[(0,[z32,z42,z1,z2,z3,z5,z8]),(0,[z645,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z646]),(0,[z1,z2,z302,z3,z5,z8,z6]),(0,[z1,z2,z3,z647,z5,z8,z6]),(0,[z1,z2,z3,z648,z5,z8,z6]),(0,[z1,z649,z2,z3,z5,z8,z6])],[(0,[z345,z2,z119,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z8,z627]),(0,[z1,z2,z3,z5,z8,z627,z6]),(0,[z650,z1,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z5,z8,z211]),(0,[z651,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z30,z14,z3,z5,z8]),(0,[z1,z652,z2,z3,z5,z8,z6])],[(1,[z1,z242,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z37,z8,z6]),(0,[z563,z42,z1,z2,z3,z5,z8])],[(0,[z345,z1,z2,z3,z5,z8,z83]),(1,[z1,z375,z2,z3,z8,z6]),(0,[z42,z1,z2,z119,z3,z5,z8]),(0,[z1,z2,z3,z5,z653,z8,z6]),(0,[z82,z1,z2,z112,z3,z5,z6]),(0,[z42,z1,z2,z3,z5,z8,z148]),(0,[z1,z2,z3,z654,z5,z8,z6])],[(1,[z132,z2,z3,z224,z8,z6]),(0,[z1,z2,z9,z3,z241,z5,z8]),(0,[z1,z138,z2,z3,z5,z8,z6]),(0,[z1,z2,z30,z5,z8,z97,z6]),(0,[z1,z2,z3,z5,z8,z655,z6]),(1,[z1,z2,z656,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z148])],[(0,[z26,z1,z2,z3,z27,z8,z6]),(0,[z1,z2,z3,z5,z8,z657,z6]),(0,[z1,z2,z658,z3,z5,z8,z6]),(0,[z42,z1,z2,z30,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z659,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z660,z6]),(0,[z661,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z241,z5,z8]),(0,[z1,z2,z3,z5,z8,z170,z6])],[(0,[z566,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z369,z5,z8,z6])],[(0,[z1,z2,z3,z662,z5,z8,z6]),(0,[z1,z663,z2,z3,z5,z8,z6]),(0,[z34,z1,z2,z3,z5,z8,z6]),(0,[z59,z1,z2,z3,z5,z8,z6])],[(1,[z13,z1,z2,z14,z5,z8]),(0,[z1,z2,z3,z664,z5,z8,z6]),(0,[z42,z1,z89,z2,z3,z5,z8]),(0,[z1,z2,z3,z665,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z140,z8]),(0,[z1,z666,z2,z3,z5,z8,z6])],[(0,[z1,z2,z667,z3,z5,z8,z6]),(0,[z201,z1,z56,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z446,z8,z6]),(0,[z44,z1,z2,z76,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z668,z6]),(0,[z132,z1,z145,z2,z3,z8,z6]),(0,[z42,z1,z2,z3,z16,z5,z8]),(0,[z1,z2,z3,z5,z8,z6,z669]),(0,[z1,z2,z670,z3,z5,z8,z6]),(0,[z42,z1,z2,z3,z5,z8,z170]),(0,[z11,z1,z2,z3,z37,z8,z6]),(0,[z1,z421,z2,z3,z5,z8,z6]),(0,[z1,z2,z656,z3,z4,z5,z8])],[(0,[z671,z1,z2,z3,z5,z8,z6]),(0,[z1,z672,z2,z3,z5,z8,z6]),(0,[z48,z1,z2,z3,z5,z187,z6])],[(0,[z1,z2,z3,z673,z5,z8,z6]),(1,[z1,z2,z534,z5,z8,z6]),(0,[z1,z2,z3,z5,z674,z8,z6]),(0,[z1,z2,z14,z3,z5,z8,z19]),(1,[z1,z2,z3,z5,z162,z6]),(0,[z42,z1,z2,z3,z5,z8,z31]),(1,[z60,z1,z2,z5,z8,z6])]],
   [[(0,[z1,z2,z675,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z31])],[(0,[z1,z2,z3,z676,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z677,z6]),(0,[z1,z2,z3,z678,z5,z8,z6]),(0,[z201,z2,z3,z5,z200,z8,z6]),(0,[z1,z2,z3,z5,z679,z8,z6]),(0,[z1,z145,z2,z3,z5,z8,z6]),(0,[z680,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z681,z5,z8,z6]),(0,[z0,z1,z138,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z682,z8,z6]),(0,[z1,z2,z217,z14,z3,z5,z8])],[(0,[z1,z2,z683,z3,z5,z8,z6]),(0,[z684,z1,z2,z3,z5,z8,z6]),(0,[z98,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z685,z3,z5,z8,z6]),(0,[z82,z42,z1,z2,z3,z5,z8]),(1,[z44,z1,z223,z2,z3,z5])],[(0,[z1,z2,z686,z3,z5,z8,z6]),(0,[z52,z239,z2,z3,z5,z8,z6]),(0,[z1,z2,z687,z3,z5,z8,z6])],[(0,[z1,z688,z2,z3,z5,z8,z6]),(0,[z689,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z14,z3,z62,z5,z8]),(0,[z0,z1,z2,z3,z5,z200,z6]),(0,[z1,z133,z2,z3,z241,z8,z6]),(0,[z1,z133,z3,z241,z5,z8,z6]),(0,[z1,z138,z2,z112,z3,z5,z6]),(0,[z1,z2,z690,z3,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z5,z8,z305,z6]),(0,[z1,z2,z3,z5,z691,z8,z6]),(0,[z1,z2,z3,z169,z5,z8,z6]),(0,[z1,z12,z2,z3,z5,z8,z6])],[(1,[z240,z1,z2,z3,z5,z8]),(0,[z1,z692,z2,z3,z5,z8,z6]),(0,[z1,z693,z2,z3,z5,z8,z6]),(1,[z1,z2,z3,z4,z6,z192])],[(0,[z1,z2,z3,z694,z5,z8,z6]),(0,[z1,z2,z3,z695,z5,z8,z6])],[(1,[z1,z2,z3,z322,z5,z8]),(0,[z132,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z5,z696,z8,z6]),(0,[z1,z138,z3,z169,z5,z8,z6]),(0,[z697,z1,z2,z3,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6,z698]),(0,[z1,z2,z699,z3,z5,z8,z6]),(0,[z201,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z700,z5,z8,z6]),(0,[z701,z1,z2,z3,z5,z8,z6])],[(0,[z702,z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z703,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z6,z704]),(0,[z1,z2,z656,z3,z5,z8,z6])],[(0,[z345,z1,z119,z3,z5,z8,z6]),(0,[z32,z1,z2,z30,z5,z8,z6]),(0,[z705,z1,z2,z3,z5,z8,z6]),(0,[z42,z1,z2,z112,z3,z5,z8]),(0,[z1,z2,z14,z3,z430,z5,z8])],[(0,[z1,z254,z2,z119,z3,z5,z6]),(0,[z42,z0,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z706,z5,z8,z6]),(0,[z1,z2,z3,z5,z40,z8,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z128,z240,z1,z2,z5,z8]),(0,[z1,z228,z2,z14,z3,z5]),(0,[z1,z3,z707,z5,z8,z6]),(0,[z1,z708,z2,z3,z5,z6]),(0,[z1,z2,z3,z99,z140,z8]),(0,[z1,z12,z709,z2,z3,z8])],[(0,[z1,z2,z710,z5,z8,z6]),(0,[z26,z2,z14,z3,z27,z8]),(0,[z711,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z712]),(0,[z1,z2,z14,z5,z8,z125]),(0,[z42,z1,z2,z219,z14,z5]),(0,[z1,z2,z111,z3,z5,z162])],[(0,[z1,z2,z713,z3,z5,z8]),(0,[z1,z56,z3,z5,z714,z6]),(0,[z1,z138,z14,z3,z169,z5]),(0,[z59,z1,z3,z86,z5,z8]),(0,[z82,z1,z2,z112,z5,z6]),(0,[z1,z2,z715,z14,z3,z5])],[(0,[z1,z89,z80,z5,z8,z211]),(0,[z716,z1,z2,z3,z5,z8]),(0,[z717,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z718,z8,z6]),(0,[z1,z719,z3,z5,z8,z6]),(0,[z1,z720,z3,z5,z8,z6]),(0,[z1,z2,z3,z140,z8,z6]),(0,[z98,z1,z421,z3,z5,z8])],[(0,[z1,z2,z721,z3,z5,z8]),(0,[z1,z2,z3,z5,z722,z6]),(0,[z1,z2,z14,z470,z5,z8]),(0,[z1,z72,z14,z3,z8,z146]),(0,[z1,z2,z3,z5,z8,z723]),(0,[z1,z2,z14,z5,z8,z97])],[(0,[z1,z2,z3,z5,z8,z724]),(0,[z1,z89,z80,z5,z8,z6])]],
   [[(0,[z1,z2,z725,z5,z8,z6]),(0,[z1,z3,z726,z5,z8,z159]),(0,[z231,z1,z2,z3,z140,z8])],[(0,[z1,z2,z3,z727,z5,z8]),(0,[z1,z2,z728,z29,z5,z6]),(0,[z1,z2,z14,z3,z5,z722]),(0,[z729,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z211]),(0,[z1,z2,z3,z730,z8,z6])],[(0,[z26,z2,z3,z27,z8,z627]),(0,[z1,z2,z3,z5,z731,z6]),(0,[z1,z2,z4,z344,z6,z192])],[(0,[z1,z2,z732,z5,z8,z6]),(0,[z1,z375,z2,z3,z8,z6]),(0,[z1,z2,z733,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z158]),(1,[z1,z707,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z734,z5,z8]),(0,[z42,z26,z2,z3,z27,z8]),(0,[z1,z2,z3,z5,z8,z735]),(0,[z1,z138,z237,z3,z5,z6]),(0,[z1,z2,z3,z5,z162,z148])],[(0,[z1,z375,z2,z118,z3,z8]),(0,[z1,z2,z112,z3,z55,z6]),(0,[z1,z2,z3,z5,z736,z8]),(0,[z66,z1,z2,z3,z5,z162]),(0,[z1,z2,z737,z14,z3,z8]),(0,[z1,z2,z14,z77,z5,z8])],[(0,[z738,z1,z2,z3,z5,z8]),(0,[z1,z739,z2,z3,z8,z6]),(0,[z291,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z55,z6])]],
   [[(0,[z42,z1,z314,z2,z3,z8]),(0,[z32,z2,z322,z62,z5,z8]),(0,[z13,z1,z2,z322,z5,z8]),(0,[z1,z138,z3,z169,z5,z6]),(0,[z1,z2,z263,z5,z97,z6]),(0,[z1,z2,z14,z3,z740,z8])],[(0,[z1,z2,z3,z5,z741,z6]),(0,[z1,z2,z3,z742,z5,z6]),(0,[z11,z1,z2,z3,z369,z8]),(0,[z1,z2,z743,z14,z5,z8]),(0,[z1,z2,z744,z5,z8,z6])],[(0,[z1,z2,z745,z5,z8,z6]),(1,[z2,z3,z5,z8,z746]),(0,[z1,z2,z747,z3,z5,z8]),(0,[z42,z1,z2,z256,z3,z5]),(0,[z1,z2,z14,z140,z8,z31])],[(0,[z748,z1,z2,z3,z5,z8]),(0,[z109,z1,z2,z14,z5,z8]),(0,[z1,z89,z14,z80,z5,z8]),(0,[z749,z2,z14,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z750]),(0,[z42,z1,z2,z3,z5,z751]),(0,[z297,z1,z2,z3,z5,z481])],[(0,[z345,z119,z14,z3,z5,z8]),(0,[z32,z1,z2,z68,z5,z8]),(0,[z1,z2,z3,z752,z5,z8]),(0,[z82,z1,z2,z219,z14,z5]),(0,[z1,z2,z330,z5,z8,z51])],[(0,[z1,z2,z534,z5,z8,z6]),(0,[z128,z1,z314,z2,z8,z6]),(1,[z2,z3,z753,z8,z6]),(0,[z60,z1,z2,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z754])]],
   [[(0,[z1,z2,z118,z534,z5,z8]),(0,[z1,z2,z3,z5,z755,z6]),(0,[z0,z45,z2,z3,z90,z6]),(0,[z1,z462,z3,z5,z8,z159]),(0,[z1,z2,z756,z3,z5,z8]),(0,[z1,z2,z3,z5,z714,z6]),(0,[z1,z2,z14,z515,z5,z8]),(0,[z1,z2,z728,z5,z97,z6])],[(0,[z1,z2,z14,z5,z8,z367]),(0,[z1,z2,z14,z3,z4,z192]),(0,[z1,z2,z14,z606,z5,z8])],[(0,[z42,z1,z254,z2,z3,z5]),(0,[z1,z2,z757,z5,z8,z6]),(0,[z1,z2,z3,z758,z8,z6]),(0,[z0,z2,z3,z55,z90,z6]),(0,[z1,z2,z14,z5,z8,z31])],[],[(0,[z42,z1,z2,z36,z37,z8])],[(0,[z1,z254,z2,z118,z3,z5]),(0,[z1,z2,z759,z5,z8,z6]),(0,[z2,z3,z5,z8,z760,z6])],[(0,[z761,z1,z2,z3,z5,z8]),(0,[z1,z2,z14,z703,z5,z8]),(0,[z26,z1,z2,z3,z300,z6]),(0,[z1,z2,z168,z37,z8,z6]),(0,[z1,z2,z14,z76,z5,z8]),(0,[z762,z60,z1,z2,z5,z8]),(0,[z1,z2,z656,z3,z4,z192])],[(0,[z1,z2,z3,z763,z5,z8]),(0,[z1,z79,z545,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z764]),(0,[z1,z2,z14,z3,z765,z8])]],
   [[(0,[z1,z2,z14,z5,z8,z305]),(0,[z1,z2,z766,z5,z8,z6]),(0,[z1,z2,z202,z14,z5,z8]),(0,[z42,z1,z2,z106,z5,z8]),(0,[z1,z2,z3,z4,z6,z192])],[(0,[z1,z2,z767,z5,z8,z6])],[(0,[z584,z1,z2,z14,z5,z8]),(0,[z13,z1,z2,z68,z5,z8]),(0,[z768,z1,z2,z3,z5,z8]),(0,[z769,z1,z2,z3,z5,z8]),(0,[z1,z2,z22,z3,z140,z8])],[(0,[z1,z2,z3,z770,z8,z6]),(0,[z1,z228,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z771,z6]),(0,[z42,z1,z2,z3,z5,z457]),(0,[z42,z1,z139,z145,z2,z3])],[(0,[z1,z12,z2,z3,z380,z8]),(0,[z1,z139,z482,z2,z3,z6])],[(0,[z1,z2,z772,z5,z8,z6]),(0,[z26,z536,z2,z3,z8,z6]),(0,[z1,z2,z3,z5,z8,z773]),(0,[z1,z2,z14,z609,z5,z8])],[(0,[z1,z2,z3,z5,z774,z6])],[(0,[z2,z3,z5,z8,z775,z6])]],
   [[(0,[z1,z2,z3,z5,z8,z776]),(0,[z18,z1,z2,z3,z5,z8]),(0,[z1,z2,z22,z14,z8,z97])],[(0,[z1,z777,z3,z5,z8,z6]),(0,[z240,z1,z2,z534,z5,z8]),(0,[z32,z61,z2,z62,z5,z8]),(0,[z1,z2,z3,z4,z485,z6]),(0,[z1,z2,z3,z5,z8,z778]),(0,[z1,z2,z5,z40,z97,z6]),(0,[z1,z2,z219,z14,z3,z140]),(0,[z11,z1,z2,z3,z140,z8]),(0,[z60,z1,z2,z4,z6,z192])],[(0,[z1,z779,z2,z3,z5,z6]),(0,[z1,z780,z3,z5,z8,z6]),(0,[z34,z2,z685,z3,z5,z8]),(0,[z1,z781,z14,z3,z5,z8]),(0,[z1,z12,z2,z3,z445,z8])],[(0,[z1,z2,z14,z74,z5,z8]),(0,[z469,z1,z2,z112,z5,z6])],[(0,[z1,z2,z3,z5,z8,z782]),(0,[z1,z2,z3,z5,z8,z783]),(0,[z1,z72,z372,z3,z8,z6]),(0,[z1,z2,z519,z14,z5,z8]),(0,[z48,z1,z2,z217,z8,z6])],[(0,[z42,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z40,z6]),(0,[z1,z2,z3,z5,z784,z6])],[(0,[z1,z2,z3,z5,z8,z785]),(0,[z46,z2,z3,z5,z8,z19]),(0,[z1,z2,z3,z786,z8,z6]),(0,[z82,z1,z2,z5,z40,z6]),(0,[z1,z2,z3,z5,z787,z8])],[(0,[z128,z1,z2,z14,z5,z8]),(0,[z32,z2,z788,z5,z8,z6]),(0,[z1,z133,z3,z241,z8,z166])]],
   [[(0,[z1,z2,z3,z5,z8,z789]),(0,[z32,z1,z2,z14,z5,z25]),(0,[z1,z133,z14,z3,z241,z8]),(0,[z1,z2,z790,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z791]),(0,[z1,z2,z3,z5,z173,z8]),(0,[z1,z2,z14,z3,z140,z162])],[(0,[z1,z2,z3,z792,z8,z6]),(0,[z1,z314,z2,z118,z3,z8]),(0,[z26,z2,z3,z180,z8,z6]),(0,[z1,z2,z553,z14,z5,z8]),(0,[z1,z709,z2,z3,z8,z148])],[(0,[z1,z2,z3,z5,z8,z793]),(0,[z1,z2,z3,z5,z8,z794])],[(0,[z1,z2,z14,z3,z5,z25]),(0,[z795,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z796]),(0,[z240,z1,z93,z2,z3,z5]),(0,[z1,z2,z3,z5,z797,z6]),(0,[z1,z798,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z799]),(0,[z42,z1,z2,z302,z5,z8]),(0,[z1,z2,z3,z800,z5,z8]),(0,[z1,z2,z801,z5,z8,z6]),(0,[z1,z2,z3,z5,z173,z162])],[(0,[z1,z2,z3,z5,z802,z6]),(0,[z42,z1,z2,z3,z5,z305]),(0,[z1,z2,z3,z5,z8,z803])],[(0,[z1,z2,z804,z3,z5,z8]),(0,[z42,z1,z2,z14,z140,z8])],[(0,[z1,z2,z112,z131,z5,z6]),(0,[z1,z79,z407,z3,z5,z8]),(0,[z11,z1,z12,z2,z3,z8])]],
   [[(0,[z1,z2,z3,z5,z8,z83]),(0,[z1,z314,z2,z534,z8,z6]),(0,[z32,z1,z2,z219,z14,z5]),(0,[z1,z133,z589,z3,z8,z6]),(0,[z1,z2,z3,z5,z805,z6]),(0,[z0,z2,z14,z3,z5,z90]),(0,[z1,z2,z3,z806,z5,z8])],[(0,[z1,z2,z3,z807,z5,z8]),(0,[z1,z2,z808,z3,z5,z6]),(0,[z809,z2,z3,z5,z8,z6]),(0,[z810,z1,z2,z3,z5,z8]),(0,[z811,z2,z3,z5,z8,z6]),(0,[z1,z2,z812,z14,z5,z8]),(0,[z1,z813,z2,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z814]),(0,[z1,z2,z3,z5,z8,z815]),(0,[z0,z2,z3,z5,z90,z6]),(0,[z1,z2,z816,z3,z55,z8]),(0,[z1,z2,z428,z5,z97,z6])],[(0,[z1,z2,z3,z5,z8,z817])],[(0,[z761,z128,z1,z2,z5,z8]),(0,[z2,z3,z5,z818,z90,z6]),(0,[z82,z1,z2,z112,z5,z161])],[(0,[z1,z2,z534,z5,z8,z796]),(0,[z1,z2,z819,z5,z8,z6]),(0,[z374,z1,z2,z14,z5,z8]),(0,[z1,z2,z3,z820,z5,z8]),(0,[z11,z1,z709,z2,z3,z8])],[(1,[z1,z2,z14,z5,z305]),(0,[z1,z2,z219,z14,z330,z5])],[(0,[z128,z1,z254,z2,z5,z6]),(0,[z1,z375,z93,z2,z3,z6]),(0,[z1,z2,z513,z5,z8,z163]),(0,[z1,z2,z3,z5,z818,z6]),(0,[z1,z2,z3,z5,z8,z746]),(0,[z1,z72,z3,z821,z8,z6])]],
   [[(0,[z1,z2,z3,z822,z5,z6]),(0,[z1,z823,z2,z3,z5,z6]),(0,[z824,z1,z2,z3,z5,z8]),(0,[z1,z2,z14,z3,z730,z8]),(0,[z825,z1,z2,z344,z5,z8])],[(0,[z1,z2,z3,z5,z826,z6]),(0,[z1,z2,z3,z821,z8,z6]),(0,[z1,z79,z3,z184,z5,z8]),(0,[z1,z2,z36,z37,z8,z6])],[(0,[z1,z2,z827,z5,z8,z6]),(0,[z34,z1,z2,z302,z5,z8]),(0,[z1,z2,z3,z5,z828,z6]),(0,[z1,z56,z3,z5,z170,z6]),(0,[z42,z1,z2,z506,z5,z8]),(1,[z1,z2,z3,z140,z162])],[(0,[z1,z254,z2,z534,z5,z6]),(0,[z1,z2,z3,z753,z8,z6]),(0,[z1,z2,z256,z14,z3,z5]),(0,[z1,z2,z22,z219,z14,z3])],[(0,[z1,z829,z3,z5,z8,z6]),(0,[z1,z2,z3,z734,z5,z8]),(0,[z830,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z831,z5,z6]),(0,[z13,z1,z2,z219,z14,z5]),(0,[z1,z2,z3,z5,z832,z6]),(0,[z1,z2,z3,z833,z5,z8]),(0,[z82,z1,z2,z112,z14,z5])],[(0,[z32,z1,z2,z322,z5,z8]),(0,[z834,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z835,z6]),(0,[z1,z12,z2,z3,z5,z162])],[(0,[z1,z836,z2,z3,z5,z6]),(0,[z1,z837,z2,z3,z5,z6]),(0,[z1,z2,z3,z838,z8,z6]),(0,[z1,z2,z3,z839,z5,z8]),(0,[z1,z2,z840,z3,z8,z6])]],
   [[(0,[z42,z0,z2,z3,z5,z90]),(0,[z1,z2,z14,z523,z5,z8]),(0,[z82,z1,z2,z728,z5,z6]),(0,[z1,z2,z14,z3,z5,z841]),(0,[z1,z2,z3,z5,z842,z6])],[(0,[z1,z2,z843,z3,z8,z6]),(0,[z1,z2,z844,z3,z5,z8]),(0,[z845,z1,z2,z5,z8,z6]),(0,[z82,z1,z2,z14,z140,z8]),(0,[z82,z1,z2,z140,z8,z6]),(0,[z1,z2,z840,z3,z6,z192]),(0,[z1,z223,z2,z3,z551,z5]),(0,[z44,z1,z813,z2,z3,z5])],[(0,[z1,z2,z3,z5,z8,z846]),(0,[z2,z3,z5,z8,z746,z20]),(0,[z1,z2,z3,z5,z847,z6]),(0,[z1,z2,z217,z434,z8,z6]),(0,[z60,z1,z2,z5,z97,z6]),(0,[z44,z1,z2,z3,z5,z162])],[(0,[z1,z2,z848,z5,z8,z6]),(0,[z1,z2,z3,z5,z849,z8]),(0,[z1,z2,z3,z140,z8,z162])],[(0,[z1,z2,z3,z5,z850,z6]),(0,[z1,z2,z3,z5,z8,z851]),(0,[z48,z1,z2,z217,z40,z6])],[(0,[z132,z2,z3,z753,z8,z6]),(0,[z852,z1,z2,z3,z8,z6]),(0,[z1,z2,z853,z5,z8,z6]),(0,[z1,z2,z854,z14,z3,z8]),(0,[z680,z1,z2,z14,z5,z8]),(0,[z42,z1,z2,z3,z5,z741])],[(0,[z855,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z856,z6]),(0,[z1,z2,z3,z5,z8,z857]),(0,[z1,z2,z3,z5,z8,z858]),(0,[z1,z2,z728,z3,z5,z6]),(0,[z1,z2,z112,z330,z5,z6])],[(0,[z42,z1,z375,z2,z3,z8]),(0,[z0,z489,z2,z3,z5,z6]),(0,[z42,z1,z2,z599,z5,z8]),(0,[z1,z133,z9,z3,z241,z8]),(0,[z1,z2,z14,z3,z859,z8])]],
   [[(0,[z345,z118,z119,z3,z5,z8]),(0,[z1,z860,z3,z5,z8,z6])],[(0,[z2,z777,z3,z5,z8,z6]),(0,[z26,z2,z3,z27,z8,z6])],[(0,[z42,z1,z2,z3,z5,z245]),(0,[z1,z2,z3,z726,z5,z8]),(0,[z1,z2,z22,z14,z3,z8]),(0,[z1,z2,z14,z5,z309,z8]),(1,[z1,z709,z2,z3,z8])],[(0,[z1,z2,z14,z5,z8,z163]),(0,[z1,z2,z14,z108,z5,z8]),(0,[z1,z2,z513,z14,z5,z8]),(0,[z1,z2,z3,z430,z140,z8]),(0,[z1,z2,z219,z3,z140,z6])],[(0,[z1,z2,z14,z17,z5,z8]),(0,[z861,z1,z2,z3,z5,z8]),(0,[z42,z1,z2,z3,z5,z40]),(0,[z1,z2,z29,z5,z97,z6]),(0,[z449,z124,z2,z3,z5,z8]),(0,[z1,z2,z862,z3,z5,z8])],[(0,[z1,z2,z3,z863,z5,z8]),(0,[z864,z1,z2,z3,z5,z8]),(0,[z1,z2,z344,z5,z8,z6]),(0,[z1,z2,z737,z3,z8,z6])],[(0,[z1,z2,z3,z865,z5,z8]),(0,[z1,z2,z3,z5,z8,z866]),(0,[z416,z2,z3,z5,z8,z19]),(0,[z42,z1,z72,z3,z8,z146]),(0,[z1,z56,z333,z3,z5,z6]),(0,[z279,z1,z2,z14,z5,z8]),(0,[z1,z2,z22,z14,z3,z162])],[(0,[z345,z128,z119,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z867]),(0,[z1,z2,z3,z5,z140,z162])]],
   [[(0,[z1,z375,z2,z534,z8,z6]),(1,[z1,z3,z5,z714,z6]),(0,[z1,z2,z868,z5,z8,z6]),(0,[z1,z2,z869,z14,z3,z5]),(0,[z1,z2,z3,z5,z481,z51])],[(0,[z1,z2,z3,z5,z870,z6]),(0,[z1,z2,z3,z871,z8,z6]),(0,[z1,z2,z3,z5,z8,z872]),(0,[z1,z2,z3,z4,z622,z6]),(0,[z87,z1,z2,z3,z456,z8])],[(0,[z1,z873,z3,z5,z8,z6]),(0,[z48,z1,z2,z217,z369,z8])],[(0,[z1,z874,z2,z3,z8,z6]),(0,[z749,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z875,z5,z8]),(0,[z1,z2,z3,z876,z8,z6]),(0,[z1,z2,z219,z3,z73,z5]),(0,[z1,z175,z2,z3,z140,z8]),(0,[z825,z1,z2,z3,z5,z8]),(0,[z297,z1,z2,z330,z5,z8])],[(0,[z1,z2,z877,z3,z5,z8]),(0,[z1,z878,z2,z3,z8,z6]),(0,[z879,z1,z2,z3,z5,z8]),(0,[z1,z3,z241,z821,z8,z6]),(0,[z1,z2,z3,z880,z5,z8]),(0,[z1,z2,z881,z5,z8,z6])],[(0,[z345,z119,z3,z5,z8,z6]),(0,[z1,z882,z2,z3,z5,z6]),(0,[z42,z1,z2,z434,z5,z8]),(0,[z42,z1,z2,z330,z5,z8])],[(0,[z1,z2,z3,z883,z5,z8]),(0,[z1,z2,z3,z369,z5,z8])],[(0,[z26,z228,z2,z3,z27,z6]),(0,[z15,z42,z1,z16,z5,z8]),(0,[z1,z2,z3,z639,z8,z148]),(0,[z1,z2,z22,z3,z162,z6])]],
   [[(0,[z1,z2,z3,z5,z8,z884]),(0,[z2,z3,z5,z753,z8,z6]),(0,[z34,z2,z302,z5,z8,z20]),(0,[z1,z2,z14,z3,z5,z885])],[(0,[z1,z2,z886,z3,z5,z8]),(0,[z1,z93,z2,z118,z3,z5]),(0,[z1,z2,z3,z300,z5,z6]),(0,[z1,z2,z3,z5,z8,z887]),(0,[z1,z2,z14,z3,z5,z187]),(0,[z1,z888,z2,z3,z5,z6])],[(0,[z1,z2,z14,z5,z97,z90]),(0,[z1,z2,z3,z889,z8,z6]),(0,[z279,z2,z3,z5,z8,z20]),(0,[z890,z1,z2,z3,z5,z8]),(0,[z891,z2,z14,z3,z5,z8])],[(0,[z777,z119,z3,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z892]),(0,[z1,z79,z2,z3,z140,z8]),(0,[z42,z1,z2,z310,z5,z8]),(0,[z1,z813,z2,z3,z5,z50])],[(0,[z1,z2,z534,z14,z5,z8]),(0,[z1,z2,z14,z3,z300,z5]),(0,[z1,z2,z3,z55,z97,z6]),(0,[z1,z3,z893,z5,z8,z6]),(0,[z1,z894,z2,z3,z8,z6]),(0,[z1,z2,z3,z895,z8,z6]),(0,[z1,z2,z3,z5,z8,z23])],[(0,[z1,z2,z3,z5,z896,z6]),(0,[z1,z2,z3,z5,z8,z897])],[(0,[z1,z2,z3,z5,z8,z898]),(0,[z1,z2,z3,z5,z8,z899]),(0,[z1,z2,z256,z3,z5,z6]),(0,[z11,z1,z2,z3,z96,z8]),(0,[z1,z2,z3,z5,z8,z900])],[(0,[z1,z2,z3,z901,z8,z6]),(0,[z15,z1,z16,z5,z8,z6]),(0,[z1,z2,z902,z3,z5,z8]),(0,[z903,z1,z2,z3,z5,z8])]],
   [[(0,[z904,z1,z2,z3,z5,z8]),(0,[z1,z905,z2,z3,z5,z6]),(0,[z15,z1,z707,z5,z8,z6]),(0,[z1,z906,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z907]),(0,[z1,z2,z3,z5,z908,z8]),(0,[z1,z2,z112,z728,z5,z6])],[(0,[z1,z2,z3,z5,z909,z6]),(0,[z1,z2,z715,z3,z5,z6]),(0,[z282,z1,z2,z36,z37,z8])],[(0,[z1,z2,z910,z5,z8,z6]),(0,[z1,z2,z911,z5,z8,z6])],[(0,[z1,z2,z3,z5,z912,z6]),(0,[z1,z2,z3,z5,z8,z913]),(0,[z1,z2,z3,z78,z8,z148]),(0,[z18,z1,z2,z30,z5,z8]),(0,[z1,z223,z2,z3,z140,z8])],[(0,[z32,z1,z2,z14,z140,z8]),(0,[z1,z2,z881,z3,z8,z6])],[(0,[z1,z2,z3,z914,z8,z6]),(0,[z13,z2,z625,z5,z8,z6]),(0,[z1,z56,z14,z3,z5,z170]),(0,[z60,z1,z2,z5,z8,z23])],[(0,[z32,z2,z62,z5,z8,z6]),(0,[z1,z2,z3,z5,z915,z6]),(0,[z2,z3,z5,z8,z19,z746]),(0,[z916,z1,z2,z3,z5,z8]),(0,[z59,z1,z191,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z917]),(0,[z1,z2,z14,z29,z5,z97]),(0,[z1,z2,z3,z5,z50,z162]),(0,[z1,z144,z2,z14,z5,z8]),(0,[z1,z2,z918,z344,z5,z8])],[(0,[z382,z1,z2,z14,z5,z8]),(0,[z1,z2,z14,z3,z140,z8]),(0,[z231,z1,z2,z219,z3,z5]),(0,[z1,z2,z743,z3,z5,z8]),(0,[z1,z2,z919,z5,z8,z6])]],
   [[(0,[z42,z1,z2,z30,z5,z8])],[(0,[z1,z2,z920,z3,z5,z8]),(0,[z1,z2,z36,z96,z37,z8]),(0,[z1,z139,z2,z840,z3,z6])],[(0,[z921,z1,z2,z5,z8,z6]),(0,[z1,z781,z3,z5,z8,z6]),(0,[z82,z1,z2,z112,z73,z5]),(0,[z82,z42,z1,z2,z112,z5])],[(0,[z1,z2,z14,z5,z305,z6]),(0,[z15,z1,z464,z16,z5,z8]),(0,[z1,z922,z2,z3,z8,z6]),(0,[z1,z2,z219,z5,z97,z6]),(0,[z44,z1,z2,z3,z5,z125])],[(0,[z923,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z924])],[(0,[z1,z2,z3,z925,z5,z8]),(0,[z13,z1,z2,z734,z5,z8]),(0,[z650,z1,z3,z86,z5,z8]),(0,[z1,z2,z112,z3,z5,z23]),(0,[z42,z1,z2,z3,z5,z926]),(0,[z44,z1,z223,z2,z76,z5])],[(0,[z1,z2,z3,z5,z927,z6]),(0,[z34,z2,z3,z5,z8,z746]),(0,[z1,z2,z3,z5,z8,z928])],[(0,[z1,z2,z3,z456,z8,z148])]],
   [[(0,[z345,z777,z3,z5,z8,z6]),(0,[z128,z1,z2,z118,z5,z8]),(0,[z32,z1,z2,z22,z14,z8]),(1,[z1,z2,z743,z5,z8]),(0,[z383,z1,z2,z3,z5,z125]),(0,[z1,z2,z929,z3,z5,z8]),(0,[z1,z2,z3,z930,z5,z8])],[(0,[z42,z1,z2,z534,z5,z8]),(0,[z13,z1,z2,z14,z140,z8]),(0,[z1,z931,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z8,z932]),(0,[z1,z3,z5,z821,z8,z6]),(0,[z1,z2,z3,z5,z8,z933])],[(0,[z1,z2,z3,z5,z8,z934]),(0,[z1,z2,z3,z935,z5,z8]),(0,[z282,z1,z2,z3,z5,z8])],[(0,[z1,z2,z3,z5,z8,z936]),(0,[z937,z1,z2,z5,z8,z6]),(0,[z1,z2,z219,z14,z5,z97])],[(0,[z1,z2,z3,z5,z8,z938])],[],[(0,[z449,z1,z2,z14,z5,z8]),(0,[z1,z2,z3,z939,z8,z6]),(0,[z1,z139,z2,z3,z10,z6]),(0,[z1,z2,z940,z14,z3,z8]),(0,[z42,z1,z2,z22,z3,z8])],[(0,[z1,z2,z3,z5,z941,z6]),(0,[z942,z1,z2,z5,z8,z6]),(0,[z1,z2,z22,z14,z8,z31]),(0,[z1,z2,z219,z3,z5,z51])]],
   [[(0,[z1,z2,z943,z5,z8,z6]),(0,[z1,z2,z3,z944,z8,z6]),(0,[z1,z138,z2,z14,z5,z97]),(0,[z1,z2,z743,z5,z8,z6])],[(0,[z1,z945,z2,z3,z5,z6]),(0,[z1,z2,z3,z946,z5,z8]),(1,[z1,z3,z821,z8,z6]),(0,[z1,z2,z73,z5,z8,z97]),(0,[z18,z1,z2,z76,z5,z8]),(0,[z42,z1,z2,z3,z4,z192])],[(0,[z1,z2,z3,z5,z947,z6]),(0,[z1,z2,z940,z3,z8,z6]),(0,[z1,z89,z707,z5,z8,z6]),(0,[z1,z2,z3,z5,z948,z6]),(0,[z1,z2,z330,z5,z8,z6]),(0,[z283,z1,z3,z184,z5,z8])],[(0,[z132,z400,z2,z3,z8,z6]),(0,[z1,z2,z3,z5,z841,z6]),(0,[z566,z1,z2,z3,z446,z8])],[(0,[z42,z1,z93,z2,z3,z5]),(0,[z1,z2,z302,z5,z8,z6]),(0,[z132,z301,z2,z3,z8,z6]),(0,[z1,z2,z949,z5,z8,z6]),(1,[z1,z2,z881,z8,z6]),(0,[z689,z1,z2,z3,z4,z6])],[(0,[z13,z1,z2,z22,z14,z8]),(0,[z950,z1,z2,z3,z5,z8]),(0,[z42,z1,z2,z623,z5,z8]),(0,[z1,z2,z951,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z952]),(0,[z42,z1,z2,z22,z14,z8]),(0,[z1,z2,z14,z311,z5,z8]),(0,[z42,z1,z2,z3,z5,z953])],[(0,[z1,z2,z3,z73,z5,z51]),(0,[z1,z2,z14,z3,z5,z162]),(0,[z1,z2,z219,z14,z3,z5]),(0,[z1,z2,z22,z219,z3,z6]),(0,[z42,z1,z2,z517,z5,z8]),(0,[z42,z1,z2,z76,z5,z8])],[(0,[z1,z93,z2,z534,z5,z6]),(0,[z1,z2,z3,z5,z954,z6]),(0,[z1,z2,z3,z955,z8,z6]),(0,[z1,z3,z726,z5,z8,z6]),(0,[z1,z2,z3,z5,z956,z6]),(0,[z1,z2,z3,z5,z8,z957])]],
   [[(0,[z345,z119,z3,z5,z8,z83]),(0,[z1,z89,z558,z5,z8,z6])],[(0,[z42,z1,z2,z3,z300,z5]),(0,[z1,z2,z958,z3,z5,z6]),(0,[z1,z2,z70,z37,z8,z6]),(0,[z1,z2,z3,z5,z8,z161])],[(0,[z1,z2,z3,z5,z8,z959]),(0,[z1,z2,z3,z5,z25,z6]),(0,[z1,z2,z3,z5,z8,z163]),(0,[z1,z960,z2,z3,z5,z8]),(0,[z1,z3,z821,z8,z146,z6]),(0,[z1,z2,z14,z5,z8,z364]),(0,[z1,z813,z2,z3,z5,z51])],[(0,[z1,z2,z961,z5,z8,z6]),(0,[z1,z2,z3,z5,z962,z6]),(0,[z1,z2,z3,z963,z8,z6]),(0,[z1,z2,z3,z5,z8,z166])],[(0,[z1,z12,z2,z302,z5,z8])],[(0,[z1,z2,z3,z5,z8,z964]),(0,[z1,z965,z2,z3,z5,z6]),(0,[z1,z2,z816,z3,z5,z8]),(0,[z48,z1,z2,z217,z14,z8]),(0,[z82,z1,z2,z14,z5,z97]),(0,[z1,z2,z261,z14,z5,z8]),(0,[z762,z1,z2,z3,z5,z8]),(0,[z11,z1,z2,z3,z446,z8])],[(0,[z92,z1,z2,z3,z5,z8]),(0,[z1,z2,z966,z3,z5,z8]),(0,[z18,z1,z2,z29,z5,z97])],[(0,[z345,z42,z119,z3,z5,z8]),(0,[z1,z2,z3,z5,z967,z6]),(0,[z1,z2,z219,z14,z5,z31])]],
   [[(0,[z1,z2,z3,z5,z8,z968]),(0,[z969,z1,z2,z3,z5,z8]),(0,[z13,z1,z2,z14,z5,z162]),(0,[z1,z2,z958,z302,z5,z6]),(0,[z970,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z96,z8]),(0,[z42,z1,z2,z14,z5,z162]),(0,[z60,z1,z2,z656,z5,z8]),(0,[z44,z1,z223,z2,z330,z5])],[(0,[z971,z1,z2,z3,z5,z8]),(0,[z82,z1,z2,z5,z96,z8]),(0,[z1,z2,z972,z5,z8,z6])],[(0,[z1,z145,z2,z3,z135,z6]),(0,[z1,z2,z14,z662,z5,z8]),(0,[z42,z1,z2,z513,z5,z8]),(0,[z1,z2,z3,z140,z8,z19]),(1,[z1,z3,z726,z5,z8]),(0,[z1,z2,z3,z5,z8,z182]),(0,[z1,z2,z14,z3,z5,z828]),(0,[z1,z2,z338,z3,z140,z8])],[(0,[z1,z2,z14,z426,z5,z8]),(0,[z1,z138,z2,z344,z5,z6]),(0,[z42,z1,z2,z29,z5,z97])],[(0,[z1,z2,z3,z973,z5,z8]),(0,[z1,z2,z3,z974,z5,z8]),(0,[z1,z2,z854,z3,z8,z6]),(0,[z1,z2,z3,z5,z975,z6])],[(0,[z32,z42,z2,z62,z5,z8]),(0,[z1,z2,z3,z976,z8,z6]),(0,[z1,z2,z3,z977,z8,z6]),(0,[z1,z978,z3,z5,z8,z6]),(0,[z1,z2,z3,z979,z8,z6]),(0,[z1,z2,z587,z5,z97,z6]),(0,[z717,z60,z1,z2,z5,z8])],[(0,[z1,z2,z3,z5,z8,z980]),(0,[z981,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z982,z5,z8]),(0,[z15,z92,z1,z16,z5,z8]),(0,[z1,z72,z3,z8,z146,z6]),(0,[z1,z2,z983,z3,z5,z8]),(0,[z1,z2,z14,z5,z8,z325]),(0,[z1,z2,z14,z3,z955,z8])],[(0,[z1,z2,z3,z984,z8,z6]),(0,[z985,z1,z2,z3,z5,z8]),(0,[z1,z254,z314,z2,z3,z6]),(0,[z1,z3,z5,z714,z8,z6]),(0,[z1,z2,z812,z3,z5,z8]),(1,[z1,z813,z2,z3,z5])]],
   [[(0,[z128,z1,z375,z2,z8,z6]),(0,[z1,z2,z3,z5,z986,z6]),(0,[z1,z987,z3,z5,z8,z6]),(0,[z82,z1,z2,z22,z14,z8]),(0,[z1,z175,z360,z3,z5,z8]),(0,[z1,z2,z14,z88,z5,z8])],[(0,[z1,z2,z22,z3,z8,z6])],[(0,[z208,z1,z2,z14,z5,z8]),(0,[z201,z1,z2,z3,z55,z6]),(0,[z1,z2,z988,z5,z8,z6]),(0,[z1,z2,z989,z3,z5,z8])],[(0,[z42,z1,z2,z3,z5,z25]),(0,[z990,z1,z2,z3,z5,z8]),(0,[z991,z1,z2,z3,z5,z8]),(0,[z1,z72,z3,z457,z146,z6])],[(0,[z1,z992,z2,z3,z5,z6]),(0,[z1,z993,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z994,z6]),(0,[z1,z2,z347,z5,z97,z6])],[(0,[z1,z2,z3,z5,z8,z995]),(0,[z1,z2,z3,z5,z996,z6]),(0,[z26,z2,z3,z300,z27,z6]),(0,[z42,z1,z138,z3,z169,z5]),(0,[z1,z3,z997,z5,z8,z6])],[(0,[z128,z1,z2,z5,z8,z6]),(0,[z1,z998,z2,z3,z8,z6]),(0,[z1,z999,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z1000]),(0,[z1,z2,z3,z1001,z5,z8]),(0,[z34,z2,z513,z5,z8,z20]),(0,[z1,z2,z3,z5,z1002,z6]),(0,[z1,z2,z399,z14,z5,z8]),(0,[z42,z1,z242,z2,z3,z5]),(0,[z1,z2,z14,z3,z963,z8]),(0,[z66,z1,z2,z22,z3,z8])],[(0,[z1,z2,z1003,z5,z8,z6]),(0,[z1,z2,z1004,z3,z5,z8]),(0,[z46,z1,z2,z302,z5,z8]),(0,[z1,z2,z1005,z5,z8,z6]),(0,[z82,z1,z2,z14,z5,z8]),(0,[z42,z1,z2,z168,z5,z8]),(0,[z42,z1,z2,z269,z5,z8])]],
   [[(0,[z1,z2,z3,z5,z8,z390]),(0,[z1,z2,z3,z5,z8,z1006]),(0,[z1,z2,z3,z5,z8,z1007]),(0,[z1008,z1,z2,z3,z5,z8]),(0,[z123,z2,z3,z5,z8,z19]),(0,[z1,z139,z145,z2,z14,z3]),(0,[z232,z279,z2,z3,z5,z8]),(0,[z1,z139,z145,z2,z3,z6])],[(0,[z1,z2,z728,z5,z8,z6]),(0,[z151,z1,z2,z14,z5,z8]),(0,[z1,z2,z3,z1009,z5,z8])],[(0,[z32,z2,z430,z5,z8,z6]),(0,[z1,z2,z3,z55,z8,z1010]),(0,[z1,z2,z3,z5,z187,z6]),(0,[z42,z48,z1,z2,z217,z8])],[(0,[z1,z2,z30,z5,z305,z6]),(0,[z1,z2,z3,z5,z1011,z6]),(0,[z1,z2,z5,z96,z8,z97]),(0,[z82,z1,z2,z14,z5,z162]),(0,[z42,z1,z2,z3,z5,z948])],[(0,[z1,z1012,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1013,z6]),(0,[z1,z2,z1014,z5,z8,z6]),(0,[z1,z421,z3,z5,z8,z159]),(0,[z1,z2,z3,z765,z8,z6])],[(0,[z1,z314,z2,z14,z3,z8]),(0,[z42,z13,z2,z58,z5,z8]),(0,[z2,z3,z5,z8,z746,z6]),(0,[z1,z242,z2,z14,z3,z5]),(0,[z1,z2,z140,z8,z97,z6])],[(0,[z61,z1,z2,z3,z5,z8]),(0,[z382,z2,z3,z5,z90,z6]),(0,[z1,z2,z217,z881,z8,z6]),(0,[z1,z2,z1015,z3,z5,z8])],[(0,[z32,z13,z2,z14,z5,z8]),(0,[z616,z1,z2,z14,z5,z8]),(0,[z1,z3,z1016,z5,z8,z6]),(0,[z1,z1017,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z40,z957]),(0,[z60,z1,z2,z14,z5,z8])]],
   [[(0,[z1,z2,z1018,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z1019]),(0,[z345,z314,z119,z3,z8,z6]),(0,[z1,z2,z3,z5,z8,z1020]),(0,[z1,z2,z302,z86,z5,z8])],[(0,[z128,z1,z93,z2,z5,z6]),(0,[z1,z1021,z2,z3,z8,z6]),(0,[z1022,z2,z3,z5,z8,z6]),(0,[z1,z2,z3,z1023,z5,z8]),(0,[z1,z2,z219,z3,z5,z6])],[(0,[z1,z2,z3,z5,z305,z6]),(0,[z132,z1,z2,z3,z300,z6]),(0,[z1,z2,z3,z140,z8,z20]),(0,[z891,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z344,z5,z8])],[(0,[z1,z56,z635,z3,z5,z6]),(0,[z1,z2,z14,z5,z200,z97]),(0,[z1,z2,z3,z5,z1024,z6])],[(0,[z1,z2,z344,z5,z8,z23])],[(0,[z1,z2,z3,z1025,z8,z6]),(0,[z0,z2,z3,z180,z5,z6]),(0,[z1,z2,z3,z5,z8,z1026]),(0,[z416,z2,z222,z3,z5,z8]),(0,[z1,z2,z1027,z3,z5,z6])],[(0,[z1028,z1,z2,z3,z5,z8]),(0,[z1,z2,z14,z569,z5,z8])],[(0,[z1,z2,z3,z1029,z5,z8]),(0,[z1,z2,z3,z5,z8,z1030]),(0,[z1,z2,z656,z344,z5,z8])]],
   [[(0,[z1,z2,z3,z5,z8,z1031]),(0,[z1,z79,z3,z5,z8,z159]),(0,[z42,z1,z2,z642,z5,z8])],[(0,[z128,z42,z1,z2,z5,z8]),(0,[z1032,z1,z2,z3,z5,z8]),(0,[z1,z133,z3,z241,z8,z6]),(0,[z59,z1,z3,z550,z5,z8]),(0,[z48,z1,z2,z217,z8,z182])],[(0,[z1,z2,z3,z5,z1033,z8]),(0,[z1,z2,z1034,z5,z8,z6]),(0,[z48,z1,z2,z881,z8,z6]),(0,[z1,z2,z1035,z3,z5,z6])],[(0,[z345,z254,z119,z3,z5,z6]),(0,[z59,z1,z425,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z1036]),(0,[z1,z2,z3,z5,z885,z6])],[(0,[z1,z2,z3,z1037,z8,z6]),(0,[z1,z2,z3,z5,z8,z1038]),(0,[z1,z89,z256,z80,z5,z6]),(0,[z1,z138,z3,z5,z714,z6]),(0,[z1,z2,z1039,z3,z5,z8]),(0,[z1,z2,z14,z4,z5,z97]),(0,[z1040,z1,z2,z5,z8,z6])],[(0,[z1,z2,z3,z5,z1041,z6]),(0,[z1,z2,z3,z1042,z5,z6]),(0,[z1,z2,z14,z3,z55,z8]),(0,[z1,z2,z1043,z5,z8,z6]),(0,[z1,z2,z3,z1044,z5,z8]),(0,[z1,z2,z3,z5,z8,z1045])],[(0,[z1,z2,z3,z1046,z5,z8]),(0,[z1,z80,z707,z5,z8,z6]),(0,[z1047,z1,z2,z3,z5,z8]),(0,[z44,z1,z2,z3,z73,z5]),(0,[z1048,z1,z2,z5,z8,z6])],[(0,[z1,z2,z3,z5,z8,z1049]),(0,[z1,z2,z3,z5,z8,z1050]),(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z2,z14,z5,z104,z8]),(0,[z1,z2,z1052,z3,z5,z6]),(0,[z1053,z2,z3,z5,z8,z6]),(0,[z1,z2,z1054,z5,z8,z6]),(0,[z1,z79,z3,z726,z5,z8]),(0,[z1,z2,z3,z5,z751,z6]),(0,[z44,z1,z2,z3,z5,z173]),(0,[z1,z2,z3,z918,z5,z8]),(0,[z1055,z1,z2,z3,z5,z8]),(0,[z1,z2,z1056,z5,z8,z6])]],
   [[(0,[z1,z2,z3,z1057,z8,z6]),(0,[z1,z2,z3,z5,z1058,z8]),(0,[z1,z2,z3,z5,z8,z1059]),(0,[z2,z3,z753,z27,z8,z6]),(0,[z42,z132,z2,z3,z224,z8])],[(0,[z1,z2,z3,z5,z1060,z6]),(0,[z1,z2,z3,z5,z1061,z6]),(0,[z1,z1062,z3,z5,z8,z6]),(0,[z1,z2,z3,z369,z8,z148])],[(0,[z1,z2,z1063,z5,z8,z6]),(0,[z1,z2,z1064,z5,z8,z6]),(0,[z42,z1,z2,z57,z5,z8])],[(0,[z1065,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z1066,z6]),(0,[z1,z2,z3,z5,z8,z84]),(0,[z1067,z2,z3,z5,z8,z6])],[],[(0,[z1,z2,z14,z373,z5,z8]),(0,[z1,z2,z1068,z14,z3,z5])],[(0,[z1,z2,z302,z5,z8,z148]),(0,[z1,z2,z869,z3,z5,z6]),(0,[z42,z60,z1,z2,z5,z8]),(1,[z1,z2,z840,z3,z6]),(0,[z1,z2,z3,z5,z306,z51])],[(0,[z1069,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z1070,z8,z6]),(0,[z201,z326,z2,z3,z5,z6])]],
   [[(0,[z240,z1,z314,z2,z3,z8]),(0,[z1,z2,z3,z740,z8,z6]),(0,[z1,z2,z14,z5,z8,z621])],[(0,[z1,z2,z3,z5,z1071,z6]),(0,[z13,z2,z608,z5,z8,z6]),(0,[z26,z2,z3,z753,z8,z6]),(0,[z1,z2,z3,z5,z953,z6]),(0,[z1,z2,z36,z14,z37,z8]),(0,[z48,z1,z2,z217,z187,z6]),(0,[z1,z2,z497,z14,z5,z8]),(0,[z1,z2,z1072,z5,z8,z6])],[(0,[z32,z1,z2,z14,z5,z8]),(0,[z1,z2,z513,z5,z8,z6]),(0,[z1,z2,z1073,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z1010]),(0,[z1,z2,z302,z5,z8,z159])],[(0,[z2,z3,z5,z8,z1074,z6])],[(0,[z1,z2,z3,z5,z457,z6]),(0,[z1,z2,z3,z5,z173,z51]),(0,[z1,z2,z743,z5,z8,z31]),(0,[z1,z223,z813,z2,z3,z5])],[(0,[z1,z2,z14,z3,z5,z8]),(0,[z1,z375,z2,z14,z3,z8]),(0,[z32,z323,z2,z5,z8,z6]),(0,[z2,z3,z224,z753,z8,z6]),(0,[z1,z860,z14,z3,z5,z8]),(0,[z42,z1,z2,z3,z5,z975])],[(0,[z32,z1,z2,z14,z5,z162]),(0,[z1,z2,z30,z5,z8,z163]),(0,[z1,z2,z3,z1075,z8,z6]),(0,[z42,z1,z89,z80,z5,z8])],[(0,[z1,z3,z1076,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z627]),(0,[z469,z1,z2,z14,z5,z8]),(0,[z1,z2,z22,z3,z369,z8])]],
   [[(0,[z345,z375,z119,z3,z8,z6]),(0,[z32,z2,z62,z5,z305,z6]),(0,[z1,z2,z1077,z3,z5,z6]),(0,[z1,z242,z2,z3,z5,z6]),(0,[z1,z1078,z2,z3,z8,z6]),(0,[z60,z1,z2,z112,z5,z6])],[(0,[z1,z2,z3,z5,z1079,z6]),(0,[z1080,z1,z2,z3,z5,z6]),(0,[z42,z1,z2,z3,z5,z187]),(0,[z1,z2,z840,z3,z4,z6])],[(0,[z240,z1,z254,z2,z3,z5]),(0,[z15,z1,z252,z5,z8,z6]),(0,[z32,z1,z2,z14,z5,z305]),(0,[z32,z2,z14,z62,z5,z8]),(0,[z132,z2,z3,z224,z8,z6]),(0,[z1,z2,z14,z391,z5,z8]),(0,[z1,z139,z2,z3,z216,z6]),(0,[z1,z133,z3,z821,z8,z6]),(0,[z18,z1,z2,z14,z5,z8]),(0,[z563,z1,z191,z3,z5,z8]),(0,[z1,z2,z656,z3,z5,z8])],[(0,[z1,z2,z1081,z5,z8,z6]),(0,[z1,z1082,z2,z3,z5,z6]),(0,[z46,z574,z2,z3,z5,z8]),(0,[z1,z2,z3,z140,z162,z6])],[(0,[z1,z2,z118,z3,z5,z8]),(0,[z1,z2,z14,z302,z5,z8]),(0,[z1,z2,z707,z5,z8,z6]),(0,[z1,z2,z1083,z5,z8,z6]),(0,[z1,z2,z14,z5,z162,z97]),(0,[z1,z2,z14,z3,z5,z962])],[(0,[z1,z2,z14,z3,z5,z305]),(0,[z1,z2,z3,z5,z8,z1084]),(0,[z1085,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z1086,z5,z8]),(0,[z46,z124,z2,z3,z5,z8]),(0,[z1,z2,z1087,z3,z5,z8]),(0,[z1,z1088,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z1089,z8]),(0,[z297,z1,z2,z14,z5,z8])],[(0,[z1,z2,z1090,z3,z5,z8]),(0,[z1,z1091,z2,z3,z5,z8]),(0,[z42,z1,z2,z743,z5,z8])],[(0,[z13,z1,z2,z14,z5,z8]),(0,[z1,z2,z3,z5,z1092,z6]),(0,[z1,z56,z2,z14,z5,z97]),(0,[z42,z1,z2,z14,z5,z8]),(0,[z42,z1,z2,z344,z5,z8])]],
   [[(0,[z1093,z1,z2,z5,z8,z6]),(0,[z1,z2,z788,z5,z8,z6]),(0,[z59,z1,z2,z3,z140,z8]),(0,[z1,z2,z14,z3,z5,z1079]),(0,[z1,z709,z2,z3,z99,z8])],[(0,[z1,z2,z3,z5,z8,z1094]),(0,[z32,z2,z14,z430,z5,z8]),(0,[z1,z175,z3,z86,z5,z8]),(0,[z297,z1,z2,z14,z5,z162]),(0,[z1,z2,z1095,z5,z8,z6])],[(0,[z1,z2,z1096,z5,z8,z6]),(0,[z1,z2,z1097,z5,z8,z6]),(0,[z1,z223,z2,z219,z3,z5])],[(0,[z1,z2,z3,z1098,z5,z6]),(0,[z1,z2,z1099,z3,z5,z6]),(0,[z46,z2,z3,z5,z8,z746]),(0,[z1,z2,z3,z5,z162,z6]),(0,[z1,z2,z3,z5,z8,z1100]),(0,[z82,z1,z2,z219,z5,z6]),(0,[z1,z2,z22,z3,z8,z148])],[(0,[z1,z254,z2,z14,z3,z5]),(0,[z1,z1101,z2,z3,z5,z6]),(0,[z1,z138,z3,z509,z5,z6])],[(0,[z1,z2,z3,z1102,z8,z6]),(0,[z1,z375,z254,z2,z3,z6]),(0,[z1,z93,z2,z14,z3,z5]),(0,[z1,z2,z3,z1103,z5,z8]),(0,[z155,z1,z2,z14,z5,z8])],[(0,[z1104,z128,z1,z2,z5,z8]),(0,[z44,z1,z2,z14,z5,z97]),(0,[z1,z12,z2,z22,z3,z8]),(0,[z1,z145,z2,z840,z3,z6]),(0,[z1,z709,z2,z3,z5,z8])],[(0,[z1,z2,z302,z5,z1011,z6]),(0,[z1,z139,z2,z14,z5,z97]),(0,[z42,z1,z2,z3,z140,z8])]],
   [[(0,[z2,z788,z62,z5,z8,z6]),(0,[z2,z3,z5,z8,z1105,z6]),(0,[z1,z2,z812,z5,z8,z97]),(0,[z1,z2,z269,z5,z97,z6]),(0,[z44,z1,z223,z2,z3,z5])],[(0,[z1,z2,z219,z330,z5,z6]),(0,[z1,z2,z30,z743,z5,z8])],[(0,[z1,z2,z3,z5,z952,z6]),(0,[z42,z1,z2,z3,z55,z8]),(0,[z1,z2,z3,z1106,z5,z8])],[(0,[z1,z93,z314,z2,z3,z6]),(0,[z1,z2,z461,z14,z5,z8]),(0,[z1,z2,z3,z5,z97,z23]),(0,[z1,z2,z3,z140,z8,z51])],[(0,[z1,z2,z1107,z3,z5,z8])],[(0,[z240,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z5,z926,z6]),(0,[z423,z2,z3,z5,z8,z20]),(0,[z1108,z1,z2,z3,z5,z8])],[(0,[z345,z240,z119,z3,z5,z8]),(0,[z1,z2,z14,z131,z5,z8]),(0,[z1,z3,z86,z726,z5,z8]),(0,[z1,z2,z222,z3,z140,z8]),(0,[z1,z2,z3,z654,z8,z148])],[(0,[z1,z2,z3,z5,z8,z1109]),(0,[z1,z2,z3,z322,z5,z8]),(0,[z1,z2,z3,z1110,z5,z8]),(0,[z1,z2,z3,z5,z8,z1111]),(0,[z0,z2,z3,z5,z818,z6]),(1,[z1,z2,z728,z5,z6])]],
   [[(0,[z1,z2,z1112,z5,z8,z6]),(0,[z1,z2,z3,z5,z8,z1113]),(0,[z1,z2,z1068,z3,z5,z6]),(0,[z34,z2,z3,z430,z5,z8]),(0,[z1,z2,z14,z5,z97,z51]),(0,[z1,z2,z14,z5,z162,z31]),(0,[z1,z2,z3,z4,z23,z192])],[(0,[z1,z2,z14,z53,z5,z8]),(0,[z1,z3,z5,z714,z170,z6]),(0,[z59,z1,z3,z726,z5,z8]),(0,[z1,z2,z14,z3,z977,z8])],[(0,[z42,z1,z228,z2,z3,z5]),(0,[z1,z56,z2,z344,z5,z6]),(0,[z1,z2,z881,z37,z8,z6])],[(0,[z1,z2,z14,z5,z8,z418]),(0,[z449,z1,z2,z302,z5,z8])],[(0,[z1,z2,z3,z1114,z8,z6]),(0,[z32,z416,z2,z14,z5,z8]),(0,[z1,z3,z1115,z5,z8,z6]),(0,[z1116,z1,z2,z5,z8,z6]),(0,[z1,z707,z16,z5,z8,z6]),(0,[z1,z2,z9,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z1117]),(0,[z1,z2,z840,z3,z5,z6]),(0,[z1,z2,z3,z1118,z5,z8])],[(0,[z1,z2,z1119,z5,z8,z6]),(0,[z42,z1,z56,z3,z5,z170]),(0,[z1,z2,z14,z3,z876,z8])],[(0,[z1,z2,z881,z36,z8,z6])],[(0,[z1,z2,z1120,z5,z8,z6]),(0,[z1,z45,z2,z14,z3,z8]),(0,[z1,z2,z3,z5,z8,z1121]),(0,[z283,z1,z2,z3,z140,z8])]],
   [[(0,[z132,z2,z14,z3,z224,z8]),(0,[z1,z2,z3,z5,z8,z1122])],[(0,[z2,z3,z788,z5,z8,z6]),(0,[z34,z2,z3,z5,z8,z20]),(0,[z1,z2,z1123,z3,z5,z6])],[(0,[z1,z2,z1124,z3,z5,z8]),(0,[z1125,z2,z3,z5,z8,z6]),(0,[z1,z2,z14,z3,z5,z245]),(0,[z1,z3,z169,z5,z714,z6]),(0,[z358,z1,z2,z14,z5,z8])],[(0,[z1,z2,z1126,z5,z8,z6]),(0,[z32,z2,z62,z5,z25,z6]),(0,[z1,z45,z2,z3,z8,z6]),(0,[z1,z2,z3,z5,z8,z1127]),(0,[z1,z89,z80,z68,z5,z8]),(0,[z1,z72,z242,z3,z146,z6]),(0,[z1,z2,z14,z3,z5,z784])],[(0,[z1,z314,z2,z3,z8,z6]),(0,[z1,z2,z3,z1128,z8,z6]),(0,[z1,z2,z3,z96,z8,z148]),(0,[z1,z2,z14,z3,z5,z40])],[(0,[z1,z2,z3,z5,z8,z1129]),(0,[z1,z2,z3,z55,z8,z6]),(0,[z1,z2,z1130,z5,z8,z6]),(0,[z42,z1,z45,z2,z3,z8]),(0,[z605,z2,z3,z5,z8,z19])],[(0,[z1,z2,z14,z341,z5,z8]),(0,[z1,z2,z29,z5,z173,z97]),(0,[z1,z1131,z2,z3,z5,z8]),(0,[z42,z1,z2,z3,z5,z162])],[(0,[z1,z2,z1132,z5,z8,z6]),(0,[z1,z2,z219,z3,z5,z162])]],
   [[(0,[z345,z119,z3,z5,z8,z390]),(0,[z1,z89,z80,z5,z245,z6]),(0,[z1,z2,z3,z4,z340,z6])],[(0,[z1,z2,z3,z68,z5,z8]),(0,[z1,z2,z3,z1133,z5,z8]),(0,[z1,z223,z2,z330,z5,z8])],[(0,[z2,z3,z5,z818,z8,z6]),(0,[z42,z1,z133,z3,z241,z8]),(0,[z1,z2,z3,z73,z5,z8])],[(0,[z1,z2,z3,z5,z1134,z6]),(0,[z1,z138,z339,z3,z5,z6]),(0,[z1,z2,z1135,z5,z8,z6]),(0,[z60,z1,z2,z5,z40,z6]),(0,[z1,z2,z76,z5,z8,z6]),(0,[z82,z1,z2,z73,z5,z8]),(0,[z42,z1,z2,z690,z5,z8])],[(0,[z1,z2,z3,z5,z1136,z6]),(0,[z1,z2,z3,z5,z8,z1137]),(0,[z1,z1088,z2,z3,z5,z40]),(0,[z1,z2,z3,z99,z8,z148])],[(0,[z1,z2,z14,z330,z5,z8])],[(0,[z1,z2,z1138,z3,z5,z8]),(0,[z1,z2,z3,z5,z8,z1139]),(0,[z614,z1,z12,z2,z3,z8]),(0,[z1,z2,z3,z5,z245,z6]),(0,[z651,z1,z2,z14,z5,z8])],[(0,[z345,z93,z119,z3,z5,z6]),(0,[z1,z254,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z28,z6]),(0,[z15,z1,z14,z16,z5,z8]),(0,[z102,z1,z2,z14,z5,z8]),(0,[z1,z709,z2,z3,z8,z6]),(0,[z1,z813,z2,z3,z5,z6])]],
   [[(0,[z1,z93,z2,z3,z5,z6]),(0,[z1,z2,z3,z96,z140,z8])],[(0,[z345,z534,z119,z5,z8,z6]),(0,[z1,z2,z108,z5,z97,z6]),(0,[z1,z56,z3,z5,z468,z6]),(0,[z1,z2,z330,z5,z97,z6])],[(0,[z1,z2,z3,z859,z8,z6])],[(0,[z1104,z1,z2,z3,z5,z8]),(0,[z1,z2,z1140,z3,z5,z8]),(0,[z1,z1141,z3,z5,z8,z6]),(0,[z641,z2,z3,z5,z8,z20]),(0,[z48,z1,z2,z337,z8,z6]),(0,[z183,z2,z3,z430,z5,z8]),(0,[z42,z1,z2,z219,z3,z5])],[(0,[z1,z1142,z2,z3,z5,z8]),(0,[z1,z1143,z2,z3,z8,z6]),(0,[z1,z2,z3,z1144,z5,z8]),(0,[z1,z2,z14,z3,z5,z1002])],[(0,[z1,z2,z3,z5,z1145,z8]),(0,[z1,z2,z3,z1146,z5,z8])],[(0,[z1,z2,z1147,z3,z5,z8]),(0,[z1,z2,z14,z5,z8,z602]),(0,[z1,z2,z3,z464,z5,z8]),(0,[z1,z2,z14,z3,z5,z457]),(0,[z1,z2,z14,z140,z8,z97]),(0,[z1,z2,z3,z5,z50,z51])],[(0,[z1,z2,z534,z807,z5,z8]),(0,[z240,z1,z375,z2,z3,z8]),(0,[z26,z2,z3,z27,z8,z84]),(0,[z1,z2,z14,z3,z1057,z8])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 525).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1058).take 143) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1201)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [525, 533, 143] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 111).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 228).take 28).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 111, 28] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_45622

theorem PEqualNP.Outside.L_meta_45622 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241376 * 2 ^ 32 + 4001933440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241376 * 2 ^ 32 + 4001933440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45622.solve