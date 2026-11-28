import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40229

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4272614016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x40000005400a8558#64 ++ 0x08000000a80150ab#64 ++ 0xb804738fc07f8fff#64 ++ 0xf7008e71f80ff1ff#64 : BitVec 256),
   (0x8419a53321a6332c#64 ++ 0xd08334a66434c665#64 ++ 0x7c3bad7323a6733d#64 ++ 0xef8775ae6474ce67#64 : BitVec 256),
   (0x02c2ca5c2c385c36#64 ++ 0x6058594b85870b86#64 ++ 0xffc3ce7c3c387c3b#64 ++ 0xdff879cf87870f87#64 : BitVec 256),
   (0x016c0f8016c06a80#64 ++ 0x802d81f002d80d50#64 ++ 0xf3fc0f803fc07fc7#64 ++ 0xbe7f81f007f80ff8#64 : BitVec 256),
   (0x01b7f0003b750007#64 ++ 0x0036fe00076ea000#64 ++ 0xe3fff0003fff8007#64 ++ 0x7c7ffe0007fff000#64 : BitVec 256),
   (0x09ff7fea80000000#64 ++ 0x013feffd50000000#64 ++ 0xedffffffc0000000#64 ++ 0xfdbffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0124000012400000 0x0024800002480000 0xe3fc00003fc00007 0x3c7f800007f80000

def z1 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc0f803fc07fc7 0xbe7f81f007f80ff8

def z2 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3ce7c3c387c3b 0xdff879cf87870f87

def z3 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0000000 0xfdbffffff8000000

def z4 : W := mkw 0x09ffffeabb750007 0x013ffffd576ea000 0xefffffffffff8007 0xfdfffffffffff000

def z5 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb804738fc07f8fff 0xf7008e71f80ff1ff

def z6 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bad7323a6733d 0xef8775ae6474ce67

def z7 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff0003fff8007 0x7c7ffe0007fff000

def z8 : W := mkw 0x8400003300021128 0x5080000660004225 0x0c00007300000038 0x0180000e60000007

def z9 : W := mkw 0x0011300001050001 0x000226000020a000 0x0000300000078000 0x000006000000f000

def z10 : W := mkw 0x02480fdc04887eb0 0xe04901fb80910fd6 0x1c000ffc00007ff8 0x838001ff80000fff

def z11 : W := mkw 0x01b7700000000000 0x0036ee0000000000 0xe1fff00000000000 0x7c3ffe0000000000

def z12 : W := mkw 0x09ff7fee80080410 0x013feffdd0010082 0xfdffffffc0380c3b 0xffbffffff8070187

def z13 : W := mkw 0x0019252200000000 0x000324a440000000 0x6c3bad7300000000 0xed8775ae60000000

def z14 : W := mkw 0x8dfffffaa1a43224 0xd1bfffff54348644 0x45fb8c7023807000 0x08bf718e04700e00

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0xa804738fc0000000 0xf5008e71f8000000

def z16 : W := mkw 0x00c24a4800000000 0x0018494900000000 0xedc3ce7c00000000 0xddb879cf80000000

def z17 : W := mkw 0x416c0f8456c8eed0 0x882d81f08ad91dda 0xf3fc5f8cffd9ffc7 0xbe7f8bf19ffb3ff8

def z18 : W := mkw 0x0800006a80000000 0x0100000d50000000 0x0c00007fc0000000 0x0180000ff8000000

def z19 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x0c03f07fc0000000 0x41807e0ff8000000

def z20 : W := mkw 0x000080003b750007 0x00001000076ea000 0x020000003fff8007 0x0040000007fff000

def z21 : W := mkw 0x08480fea80000000 0x010901fd50000000 0x0c000fffc0000000 0x818001fff8000000

def z22 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43fb80003f800000 0x087f700007f00000

def z23 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1800038fc0000ff8 0x83000071f80001ff

def z24 : W := mkw 0x09e65ac880000000 0x013ccb5910000000 0x81c4528cc0000000 0x10388a5198000000

def z25 : W := mkw 0x8400801121a6332c 0xd08010022434c665 0x1000000023a6733d 0x020000000474ce67

def z26 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x1c03ce7c00387c38 0xc38079cf80070f87

def z27 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x743b8d7023807305 0xae8771ae04700e60

def z28 : W := mkw 0x84480fb304827ba8 0xd08901f660904f75 0x1c000ff300007ff8 0x838001fe60000fff

def z29 : W := mkw 0x41b7f0057b7f855f 0x0836fe00af6ff0ab 0xfbfff38fffff8fff 0xff7ffe71fffff1ff

def z30 : W := mkw 0x85bff5333bf7332f 0xd0b7fea6677ee665 0xfffffd733ffff33f 0xffffffae67fffe67

def z31 : W := mkw 0x01ffff803ff56a87 0x803ffff007fead50 0xf3ffff803fffffc7 0xfe7ffff007fffff8

def z32 : W := mkw 0x0811302280000000 0x0102260450000000 0x00003003c0000000 0x0000060078000000

def z33 : W := mkw 0x87ffefff3ffe7fbe 0xf0fffdffe7ffcff7 0xffffefff3ffe7fff 0xfffffdffe7ffcfff

def z34 : W := mkw 0x40480f85448aefd8 0x880901f0a8915dfb 0x18000f8fc0007ff8 0x830001f1f8000fff

def z35 : W := mkw 0x036c0fdc16c87eb0 0xe06d81fb82d90fd6 0xfffc0ffc3fc07fff 0xbfff81ff87f80fff

def z36 : W := mkw 0x8408053300823328 0xd08100a660104665 0x7c380d732380733d 0xaf8701ae64700e67

def z37 : W := mkw 0xc411a037612e957c 0x58823406ec25d2af 0xbc07f3ffc07f8fff 0xf780fe7ff80ff1ff

def z38 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3ffd7323fff33f 0xff87ffae647ffe67

def z39 : W := mkw 0x0924108080000000 0x0124821010000000 0x00041080c0000000 0x0000821018000000

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x70000c0020007001 0x8e00018004000e00

def z41 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffffffffffc07fc7 0xfffffffffff80ff8

def z42 : W := mkw 0x8dfffffbb7e67bac 0xd1bfffff76fccf75 0xffffffffffe67fff 0xfffffffffffccfff

def z43 : W := mkw 0x02400a5c04085c30 0x6048014b80810b86 0x1c000e7c00007c38 0x838001cf80000f87

def z44 : W := mkw 0x03f7fa5c3f7d5c37 0x607eff4b87efab86 0xfffffe7c3ffffc3f 0xffffffcf87ffff87

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0xa804738fc07f8007 0xf5008e71f80ff000

def z46 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0x10000f8000007fc0 0x820001f000000ff8

def z47 : W := mkw 0x416c0f8556caefd8 0x882d81f0aad95dfb 0xfbfc7f8fffffffff 0xff7f8ff1ffffffff

def z48 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x4dfbfc7fc0000000 0x49bf7f8ff8000000

def z49 : W := mkw 0x0000801020201024 0x4000100204040204 0x7c038c7020207039 0xcf80718e04040e07

def z50 : W := mkw 0x0135300013450001 0x0026a6000268a000 0x003c300003c78004 0x200786000078f000

def z51 : W := mkw 0x00c2ca4828300006 0x0018594905060000 0xefc3ce7c3c380003 0xddf879cf87870000

def z52 : W := mkw 0x016c8f803ff56a87 0x802d91f007fead50 0xf3fc0f803fffffc7 0xbe7f81f007fffff8

def z53 : W := mkw 0x01b770001b550003 0x0036ee00036aa000 0x83fc70001fdf8006 0x307f8e0003fbf000

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000400fc7 0x02000000000801f8

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800700fc0000000 0x41000e01f8000000

def z56 : W := mkw 0x0000000400080410 0x0000000080010082 0x1800020c00000c38 0x8300004180000187

def z57 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb804038fc0400fff 0xb7008071f80801ff

def z58 : W := mkw 0x03e65a4c1e594c13 0x207ccb4983cb2982 0x83c4520c1c598c02 0x10788a41838b3180

def z59 : W := mkw 0x01a650001a510003 0x0034ca00034a2000 0x83c450001c598002 0x10788a00038b3000

def z60 : W := mkw 0x0000000400080410 0x0000000080010082 0x1000000000380c3b 0x0200000000070187

def z61 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xc7c3ce7c3c187c02 0x18f879cf87830f80

def z62 : W := mkw 0x85bff5323bf53227 0xd0b7fea6477ea644 0x47fb8c703f807000 0x08ff718e07f00e00

def z63 : W := mkw 0x8d3db5b3a1a6332c 0xd1a7b6b67434c665 0x7c3fbdf3e3a6733d 0xef87f7be7c74ce67

def z64 : W := mkw 0x42c2ca5d6c3add7e 0x6858594bad875baf 0xffc7fffffc7fffff 0xfff8ffffff8fffff

def z65 : W := mkw 0x8419252301862308 0x908324a46030c461 0x0038210303860304 0x200704206070c060

def z66 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x10000000007f8fff 0x02000000000ff1ff

def z67 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z68 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x43f80c003f807000 0x087f018007f00e00

def z69 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0xac07f3ffc0000000 0xf580fe7ff8000000

def z70 : W := mkw 0x00408a1024205824 0x4008114204840b04 0xffc38e703c207c3b 0xdff871ce07840f87

def z71 : W := mkw 0x8400801137e67bac 0xd080100226fccf75 0x120000003fe67fff 0x0240000007fccfff

def z72 : W := mkw 0x012c058012c02280 0x802580b002580450 0x0038000003800000 0x0007000000700000

def z73 : W := mkw 0x0019252200802200 0x800324a440100440 0x7c3bad7323807305 0xef8775ae64700e60

def z74 : W := mkw 0x0ad3fa7eac385c36 0x615a7f4fd5870b86 0xffc3fe7ffc387c3b 0xdff87fcfff870f87

def z75 : W := mkw 0x03e6cadc3e785cb6 0x607cd95b87cf0b96 0xffc7cefc3c787cfb 0xdff8f9df878f0f9f

def z76 : W := mkw 0x4093f005693f855f 0x08127e00ad27f0ab 0x0803f00fc03f8038 0x41007e01f807f007

def z77 : W := mkw 0x0000000100020108 0x0000000020004021 0xb8047103007f833f 0xf7008e20600ff067

def z78 : W := mkw 0x03e6da5c3e795c37 0x607cdb4b87cf2b86 0xffc7de7c3c79fc3b 0xdff8fbcf878f3f87

def z79 : W := mkw 0xc4192527418ea758 0x988324a4e831d4eb 0xb83c738fc3ff8fff 0xf7078e71f87ff1ff

def z80 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc7defcfc79fcfb 0xdff8fbdf9f8f3f9f

def z81 : W := mkw 0x00400a4800000000 0x0008014900000000 0x0c000e7c00000000 0x818001cf80000000

def z82 : W := mkw 0x01ff7f8016c06a80 0x803feff002d80d50 0xf3ffff803fc07fc7 0xfe7ffff007f80ff8

def z83 : W := mkw 0x01b7f00021240004 0x0036fe0004248000 0xe1fff00023a60005 0x7c3ffe000474c000

def z84 : W := mkw 0x0000000016c06a80 0x8000000002d80d50 0x120000003fc07fc7 0x0240000007f80ff8

def z85 : W := mkw 0x8419252201842200 0x908324a440308440 0x0038000003800000 0x0007000000700000

def z86 : W := mkw 0x01b7f0003ff56a87 0x8036fe0007fead50 0xf3fff0003fffffc7 0x7e7ffe0007fffff8

def z87 : W := mkw 0x02c24a4c0c184c12 0x2058494981830982 0x83c0420c1c180c02 0x1078084183830180

def z88 : W := mkw 0x0093f00029350007 0x00127e000526a000 0xa007f000007f8007 0x7400fe00000ff000

def z89 : W := mkw 0x016c0f8004806a80 0x802d81f000900d50 0xf1fc0f8000007fc0 0xbe3f81f000000ff8

def z90 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0x47c38c703c007000 0x08f8718e07800e00

def z91 : W := mkw 0x0bfffffeac385c36 0x617fffffd5870b86 0xfffbce7c3c387c3b 0xdfff79cf87870f87

def z92 : W := mkw 0x8dfffffba1a6332c 0xd1bfffff7434c665 0xfdffffffe3a6733d 0xffbffffffc74ce67

def z93 : W := mkw 0x09bf75ea80000000 0x0137eebd50000000 0x0c3ff1ffc0000000 0x6187fe3ff8000000

def z94 : W := mkw 0x0082404800000000 0x0010480900000000 0x0c03c07c00000000 0x4180780f80000000

def z95 : W := mkw 0x00c2ca002c304806 0x0018594005860900 0xf3c3ce003c387c03 0xde7879c007870f80

def z96 : W := mkw 0x8c9bf57ba1a6332c 0xd1937eaf7434c665 0x7c3bfd7fe3a6733d 0xef877faffc74ce67

def z97 : W := mkw 0x09ff7fea93450001 0x013feffd5268a000 0xedffffffc3c78004 0xfdbffffff878f000

def z98 : W := mkw 0x08480fea80000000 0x010901fd50000000 0x04000c7000000000 0x0080018e00000000

def z99 : W := mkw 0x85bff5233bf7230f 0x90b7fea4677ee461 0xe3fff1033fff8307 0x7c7ffe2067fff060

def z100 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff0003f800000 0x7c7ffe0007f00000

def z101 : W := mkw 0x03eecfdc3ef87eb6 0xe07dd9fb87df0fd6 0xffffcffc3ff87fff 0xfffff9ff87ff0fff

def z102 : W := mkw 0x8408053300823328 0xd08100a660104665 0x1c000d7300007338 0x838001ae60000e67

def z103 : W := mkw 0x01f7fa803f754887 0x003eff5007eea910 0xe3fff2803fff8cc7 0x7c7ffe5007fff198

def z104 : W := mkw 0x8dff7ffb80823328 0xd1bfefff70104665 0xfdffffffc0007338 0xffbffffff8000e67

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0xb004038000400fc7 0xb6008070000801f8

def z106 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7cffc3c787fff 0xfff8f9ff878f0fff

def z107 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0047000007f8007 0x74008e00000ff000

def z108 : W := mkw 0x84dbef7b21a6332c 0xd09b7def6434c665 0xfdfbef7f23a6733d 0xffbf7defe474ce67

def z109 : W := mkw 0x86dbef7f2dbe7f3e 0xf0db7defe5b7cfe7 0xfffbef7f3fbe7f3f 0xffff7defe7f7cfe7

def z110 : W := mkw 0x01a6d0003a710007 0x0034da00074e2000 0xe3c7d0003c798003 0x5c78fa00078f3000

def z111 : W := mkw 0x0be6dadcac385c36 0x617cdb5b95870b86 0xffc7defcfc387c3b 0xdff8fbdf9f870f87

def z112 : W := mkw 0x00c24a4800000000 0x0018494900000000 0xedc7ffffc0000000 0xfdb8fffff8000000

def z113 : W := mkw 0x0008050000000000 0x000100a000000000 0x60380d0000000000 0xac0701a000000000

def z114 : W := mkw 0x0082c00028300006 0x0010580005060000 0xe3c3c0003c380003 0x5c78780007870000

def z115 : W := mkw 0x016c8f9036e07aa4 0xc02d91f206dc0f54 0xffff8ff03fe07fff 0xfffff1fe07fc0fff

def z116 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x45fb8c7000000000 0x08bf718e00000000

def z117 : W := mkw 0x03eecfdc3ef87eb6 0xe07dd9fb87df0fd6 0xfffbce7c3fb87c3b 0xdfff79cf87f70f87

def z118 : W := mkw 0x8411a0332126112c 0x508234066424c225 0x7c03ac7320267039 0xcf80758e6404ce07

def z119 : W := mkw 0x0282c05c28381436 0x6050580b85070286 0x0c03c07c00380038 0x4180780f80070007

def z120 : W := mkw 0x49ff7fefc00a8558 0x093feffdf80150ab 0xfdffffffc07f8fff 0xffbffffff80ff1ff

def z121 : W := mkw 0x03f7fa583f755827 0x607eff4b07eeab04 0xe7fffc703ffff007 0x7cffff8e07fffe00

def z122 : W := mkw 0xc419a53761aeb77c 0xd88334a6ec35d6ef 0xfc3fffffe3ffffff 0xff87fffffc7fffff

def z123 : W := mkw 0x840080113bf7332f 0xd0801002277ee665 0x120000003ffff33f 0x0240000007fffe67

def z124 : W := mkw 0x49e65acdc00a8558 0x093ccb59b80150ab 0xb9c4738fc07f8fff 0xf7388e71f80ff1ff

def z125 : W := mkw 0x4000000440088450 0x080000008801108a 0x8004528cc0598cc2 0x10008a51980b3198

def z126 : W := mkw 0x012c058012c02280 0x802580b002580450 0x003c018003c003c4 0x2007803000780078

def z127 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x0800700fc03f8038 0x41000e01f807f007

def z128 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3faff323e67fff 0xff87f5fe647ccfff

def z129 : W := mkw 0x4000000140028148 0x0800000028005029 0x00043183c04783c4 0x200086307808f078

def z130 : W := mkw 0x00400a0004004800 0x0008014000800900 0xf3c00e003c007c03 0x9e7801c007800f80

def z131 : W := mkw 0x8411a0332126112c 0x508234066424c225 0x0c03a07300260038 0x4180740e6004c007

def z132 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc7f803fffffc7 0xfe7f8ff007fffff8

def z133 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x93c40f801c407fc2 0x927881f003880ff8

def z134 : W := mkw 0x020080142c385c36 0x6040100285870b86 0x120000003c387c3b 0x0240000007870f87

def z135 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xfbfc7f8fffc07fc7 0xff7f8ff1fff80ff8

def z136 : W := mkw 0x01bff5803bf52287 0x8037feb0077ea450 0xe3fff1803fff83c7 0x7c7ffe3007fff078

def z137 : W := mkw 0x01640a8016404880 0x002c815002c80910 0x83c402801c400cc2 0x1078805003880198

def z138 : W := mkw 0x0000000100020108 0x0000000020004021 0x0000210300060304 0x200004206000c060

def z139 : W := mkw 0x0000800020200004 0x0000100004040000 0x6003800020200001 0x4c00700004040000

def z140 : W := mkw 0x096c0fea80000000 0x012d81fd50000000 0xedfc0fffc0000000 0xbdbf81fff8000000

def z141 : W := mkw 0x8408851121a6332c 0xd08110a22434c665 0x70380d0023a6733d 0xae0701a00474ce67

def z142 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1800038fc07f8fff 0x83000071f80ff1ff

def z143 : W := mkw 0x097d3fa296c06a80 0x812fa7f452d80d50 0xf3fc3f83ffc07fc7 0xbe7f87f07ff80ff8

def z144 : W := mkw 0x0000000400080410 0x0000000080010082 0xb800420c00380c3b 0xd700084180070187

def z145 : W := mkw 0x01a6d0003b750007 0x0034da00076ea000 0x83c450003fff8007 0x10788a0007fff000

def z146 : W := mkw 0x0000000004004800 0x0000000000800900 0x120000003c007c03 0x0240000007800f80

def z147 : W := mkw 0x012480003b750007 0x00249000076ea000 0xe3fc00003fff8007 0x3c7f800007fff000

def z148 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xefffffffff807000 0xfdfffffffff00e00

def z149 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0x7fc38c703c207039 0xcff8718e07840e07

def z150 : W := mkw 0x86dbef7e2dbc7e36 0xf0db7defc5b78fc6 0xfffbce7c3fb87c3b 0xdfff79cf87f70f87

def z151 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x5fc38e7c3c007c38 0x8bf871cf87800f87

def z152 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x443b8c7023807000 0x0887718e04700e00

def z153 : W := mkw 0x0124000012400000 0x0024800002480000 0x003c000003c00004 0x2007800000780000

def z154 : W := mkw 0x01ff7f8000000000 0x003feff000000000 0xe1ffff8000000000 0xfc3ffff000000000

def z155 : W := mkw 0x49ff7fefd6caefd8 0x893feffdfad95dfb 0xffffffffffffffff 0xffffffffffffffff

def z156 : W := mkw 0x0008050000802200 0x800100a000100440 0x70380d0023807305 0xae0701a004700e60

def z157 : W := mkw 0x09b7f06abb750007 0x0136fe0d576ea000 0xeffff07fffff8007 0x7dfffe0ffffff000

def z158 : W := mkw 0x0000000100020108 0x0000000020004021 0x1800010300000338 0x8300002060000067

def z159 : W := mkw 0x017daf8037e46a84 0x802fb5f006fc8d50 0xf3ffaf803fe67fc7 0xfe7ff5f007fccff8

def z160 : W := mkw 0x09ffffeabb750007 0x013ffffd576ea000 0xe7fffc703fff8007 0x7cffff8e07fff000

def z161 : W := mkw 0x012c058000000000 0x002580b000000000 0x003c018000000000 0x2007803000000000

def z162 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000200000260005 0x640004000004c000

def z163 : W := mkw 0x0093f00029350007 0x00127e000526a000 0x0003800000000000 0x0000700000000000

def z164 : W := mkw 0x01f7fa003f754807 0x003eff4007eea900 0xf3fffe003ffffc07 0xfe7fffc007ffff80

def z165 : W := mkw 0x8419a52321a6230c 0x908334a46434c461 0x603ba10323a60305 0x6c0774206474c060

def z166 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x53f80f803f807fc0 0x8a7f01f007f00ff8

def z167 : W := mkw 0x0be65acc8c184c12 0x217ccb5991830982 0x83c4528cdc180c02 0x10788a519b830180

def z168 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800210300000000 0xe500042060000000

def z169 : W := mkw 0x0bfffffaac305826 0x617fffff55860b04 0xeffffffffc007000 0xfdffffffff800e00

def z170 : W := mkw 0x0000000100020108 0x0000000020004021 0xb804738fc026033d 0xf7008e71f804c067

def z171 : W := mkw 0x09e65ac880000000 0x013ccb5910000000 0xa9c4738fc0000000 0xf5388e71f8000000

def z172 : W := mkw 0x03ffffdc3ffd7eb7 0xe07ffffb87ffafd6 0xfffffffc3fffffff 0xffffffff87ffffff

def z173 : W := mkw 0x857dafb237e47aa4 0xd0afb5f646fc8f54 0x47fb8c703f807000 0x08ff718e07f00e00

def z174 : W := mkw 0x4000000140028148 0x0800000028005029 0xa0047183c07f83c7 0x74008e30780ff078

def z175 : W := mkw 0x0011a00021240004 0x0002340004248000 0x603ba00023a60005 0x6c0774000474c000

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x3800000000200039 0xc700000000040007

def z177 : W := mkw 0x09f7fac8bb750007 0x013eff59176ea000 0xe3fff28cffff8007 0x7c7ffe519ffff000

def z178 : W := mkw 0x09b7706a80000000 0x0136ee0d50000000 0xedfff07fc0000000 0x7dbffe0ff8000000

def z179 : W := mkw 0x09ff7fea84004800 0x013feffd50800900 0xfffffffffc007c03 0xffffffffff800f80

def z180 : W := mkw 0x8419a53337e67bac 0xd08334a666fccf75 0x7e3bad733fe67fff 0xefc775ae67fccfff

def z181 : W := mkw 0x0000000100020108 0x0000000020004021 0xb804238300660fff 0xf7008470600cc1ff

def z182 : W := mkw 0x86480f7f048a7f38 0xf0c901efe0914fe7 0x1c000f7f00007f38 0x838001efe0000fe7

def z183 : W := mkw 0x0135b00033650005 0x0026b600066ca000 0x603fb00023e78005 0x6c07f600047cf000

def z184 : W := mkw 0x49ffffeffb7f855f 0x093ffffdff6ff0ab 0xffffffffffff8fff 0xfffffffffffff1ff

def z185 : W := mkw 0xc41925234186a348 0x988324a46830d469 0x003c3183c3c783c4 0x200786307878f078

def z186 : W := mkw 0x8459afb325a67bac 0xd08b35f664b4cf75 0x7c3baff323a67ffd 0xef8775fe6474cfff

def z187 : W := mkw 0x4893706fc00a8558 0x09126e0df80150ab 0xbc07f3ffc07f8fff 0xf780fe7ff80ff1ff

def z188 : W := mkw 0x0019252200000000 0x000324a440000000 0x0038210300000000 0x2007042060000000

def z189 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3fffffe3a6733d 0xff87fffffc74ce67

def z190 : W := mkw 0x000080003b750007 0x00001000076ea000 0xa20470003fff8007 0x74408e0007fff000

def z191 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffc0400fc7 0xffbffffff80801f8

def z192 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x6dfbad7300000000 0xedbf75ae60000000

def z193 : W := mkw 0x00400a0016c06a80 0x8008014002d80d50 0xf3c00e003fc07fc7 0x9e7801c007f80ff8

def z194 : W := mkw 0x01bff5003bf52207 0x8037fea0077ea440 0xf3fffd003ffff307 0xfe7fffa007fffe60

def z195 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0xf3c00f803c007fc3 0x9e7801f007800ff8

def z196 : W := mkw 0x0bfffffeac385c36 0x617fffffd5870b86 0xfffffffffc387c3b 0xffffffffff870f87

def z197 : W := mkw 0x86c2ca5d2dbe7f3e 0xf0d8594ba5b7cfe7 0xffc3ce7c3fbe7f3f 0xdff879cf87f7cfe7

def z198 : W := mkw 0xc4080537408ab778 0xd88100a6e81156ef 0x1c000fffc0007ff8 0x838001fff8000fff

def z199 : W := mkw 0x0282404c08180412 0x2050480981030082 0x0000400c00180000 0x0000080180030000

def z200 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc07f8007 0xfdbffffff80ff000

def z201 : W := mkw 0x493d35a7c00a8558 0x0927a6b4f80150ab 0xb83c738fc07f8fff 0xf7078e71f80ff1ff

def z202 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x57c38c703c387c3b 0x0af8718e07870f87

def z203 : W := mkw 0x8dfffffbbbf7332f 0xd1bfffff777ee665 0xfffffffffffff33f 0xfffffffffffffe67

def z204 : W := mkw 0x0124000016c06a80 0x8024800002d80d50 0xf3fc00003fc07fc7 0x3e7f800007f80ff8

def z205 : W := mkw 0x4135300153478149 0x0826a6002a68f029 0x003c3183c3c783c4 0x200786307878f078

def z206 : W := mkw 0x016c0f8012c02280 0x802d81f002580450 0xe1fc0f8003c003c4 0xbc3f81f000780078

def z207 : W := mkw 0x416c0f8156c2ebc8 0x882d81f02ad85d79 0xf3fc3f83ffc7ffc7 0xbe7f87f07ff8fff8

def z208 : W := mkw 0x020080143ef87eb6 0xe040100287df0fd6 0x120000003ff87fff 0x0240000007ff0fff

def z209 : W := mkw 0x08d37a6a80000000 0x011a6f4d50000000 0xedc3fe7fc0000000 0xddb87fcff8000000

def z210 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xebfff38fffff8007 0xfd7ffe71fffff000

def z211 : W := mkw 0x01ffff803b750007 0x003ffff0076ea000 0xe3ffff803fff8007 0xfc7ffff007fff000

def z212 : W := mkw 0x40c24a4d400a8558 0x08184949a80150ab 0xfdc7ffffc07f8fff 0xffb8fffff80ff1ff

def z213 : W := mkw 0x016c0f8416c86e90 0x802d81f082d90dd2 0xfbfc4f8c3ff87fff 0xff7f89f187ff0fff

def z214 : W := mkw 0x02c24a4c0c184c12 0x2058494981830982 0xefc3ce7c1c180c02 0xddf879cf83830180

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0x6038000023800005 0x2c07000004700000

def z216 : W := mkw 0x09e65ac896404880 0x013ccb5912c80910 0x83c4528cdc400cc2 0x10788a519b880198

def z217 : W := mkw 0x02c2ca5c3ef87eb6 0xe058594b87df0fd6 0xffc3ce7c3ff87fff 0xdff879cf87ff0fff

def z218 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x7c3b8c7023a07039 0xcf87718e04740e07

def z219 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x543b8c7023a6733d 0x0a87718e0474ce67

def z220 : W := mkw 0x85b7f0113bf7332f 0xd0b6fe02277ee665 0xf3fff0003ffff33f 0x7e7ffe0007fffe67

def z221 : W := mkw 0x0000000400080410 0x0000000080010082 0xb804438c00780fff 0xf7008871800f01ff

def z222 : W := mkw 0x0000000100020108 0x0000000020004021 0x380021030026033d 0xe70004206004c067

def z223 : W := mkw 0x0011200000000000 0x0002240000000000 0x603ba00000000000 0x6c07740000000000

def z224 : W := mkw 0x03f7fa5c3f7d5c37 0x607eff4b87efab86 0xfffbce7c3fb87c3b 0xdfff79cf87f70f87

def z225 : W := mkw 0x0bff7fee8c184c12 0x217feffdd1830982 0xefffffffdc180c02 0xfdfffffffb830180

def z226 : W := mkw 0x4000000140028148 0x0800000028005029 0x38043183c06783fd 0xe7008630780cf07f

def z227 : W := mkw 0x416c0f85400a8558 0x082d81f0a80150ab 0xf9fc7f8fc07f8fff 0xff3f8ff1f80ff1ff

def z228 : W := mkw 0x857dafb337e67bac 0xd0afb5f666fccf75 0xffffaff33fe67fff 0xfffff5fe67fccfff

def z229 : W := mkw 0x0acacffeac385c36 0x615959ffd5870b86 0xffc3cffffc387c3b 0xdff879ffff870f87

def z230 : W := mkw 0x0082c01028301026 0x4010580205060204 0xffc3cc703c38703b 0xdff8798e07870e07

def z231 : W := mkw 0x0082400008100002 0x0010480001020000 0x83c040001c180002 0x1078080003830000

def z232 : W := mkw 0x41a650055a5b855b 0x0834ca00ab4b70ab 0xbbc4738fdc7f8fff 0xf7788e71fb8ff1ff

def z233 : W := mkw 0x00480f8000000000 0x000901f000000000 0x00000f8000000000 0x800001f000000000

def z234 : W := mkw 0x0011202200000000 0x0002240440000000 0x0c03a07300000000 0x4180740e60000000

def z235 : W := mkw 0x0124000012400000 0x0024800002480000 0xe3fc70003fff8007 0x7c7f8e0007fff000

def z236 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xe5ff8ff000000000 0xbcbff1fe00000000

def z237 : W := mkw 0x849be53329b6332e 0xd0937ca66536c665 0xfffbed733fbe733f 0xffff7dae67f7ce67

def z238 : W := mkw 0x09ff7fea92400000 0x013feffd52480000 0xefffffffffc00007 0xfdfffffffff80000

def z239 : W := mkw 0x00c24a4804004800 0x0018494900800900 0xffc3ce7c3c007c03 0xdff879cf87800f80

def z240 : W := mkw 0x8419a5332126112c 0x508334a66424c225 0x6c3bad7300260038 0xed8775ae6004c007

def z241 : W := mkw 0x0200001404085c30 0x6040000280810b86 0x1000000000007c38 0x0200000000000f87

def z242 : W := mkw 0x412c058152c2a3c8 0x882580b02a585479 0x003c3183c3c783c4 0x200786307878f078

def z243 : W := mkw 0x03f7fa5c2c385c36 0x607eff4b85870b86 0xfffffe7c3c387c3b 0xffffffcf87870f87

def z244 : W := mkw 0x02408a142c385c36 0x6048114285870b86 0xf3c00e003c387c3b 0x9e7801c007870f87

def z245 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43fbf0003fbf8000 0x487f7e0007f7f000

def z246 : W := mkw 0x080805a280000000 0x010100b450000000 0x00000183c0000000 0x0000003078000000

def z247 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x643bac7023a67005 0x6c87758e0474ce00

def z248 : W := mkw 0x09ff7fea9a510003 0x013feffd534a2000 0xefffffffdc598002 0xfdfffffffb8b3000

def z249 : W := mkw 0x0a93f07ea8381436 0x61527e0fd5070286 0x0c03f07fc0380038 0x41807e0ff8070007

def z250 : W := mkw 0x86dbef7a2db47a26 0xf0db7def45b68f44 0x47fb8c703f807000 0x08ff718e07f00e00

def z251 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7fffffc387c3b 0xfff8ffffff870f87

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004528cc0000000 0x10008a5198000000

def z253 : W := mkw 0x49e65accc0088450 0x093ccb599801108a 0x81c4528cc0598cc2 0x10388a51980b3198

def z254 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xa804700fc07f803f 0x75008e01f80ff007

def z255 : W := mkw 0x089b756a80000000 0x01136ead50000000 0x6c3bfd7fc0000000 0xed877faff8000000

def z256 : W := mkw 0x02400a4c04084c10 0x2048014980810982 0x0000020c00000c00 0x0000004180000180

def z257 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x1038210323a6733d 0x220704206474ce67

def z258 : W := mkw 0x4bffffffec3add7e 0x697ffffffd875baf 0xfffffffffc7fffff 0xffffffffff8fffff

def z259 : W := mkw 0x02c2ca5d2c3a5d3e 0x6058594ba5874ba7 0xffc3ef7f3c3e7f3f 0xfff87defe787cfe7

def z260 : W := mkw 0x0000000012400000 0x0000000002480000 0x020000003fc00007 0x0040000007f80000

def z261 : W := mkw 0x03e64acc1e584c92 0x207cc95983cb0992 0x83c4428c1c580cc2 0x10788851838b0198

def z262 : W := mkw 0x09ff7fea92c02280 0x813feffd52580450 0xedffffffc3c003c4 0xfdbffffff8780078

def z263 : W := mkw 0x86d3ea7f2d3e5d3e 0x70da7d4fe5a7cba7 0xffc3ee7f3c3e7c3b 0xdff87dcfe787cf87

def z264 : W := mkw 0x000080003b750007 0x00001000076ea000 0x020000003f800000 0x0040000007f00000

def z265 : W := mkw 0x01a650001a510003 0x0034ca00034a2000 0xa3c470001c7f8007 0x74788e00038ff000

def z266 : W := mkw 0x0200801428381436 0x6040100285070286 0x0000000000380038 0x0000000000070007

def z267 : W := mkw 0x09ffffeabb750007 0x013ffffd576ea000 0xefffffffff800000 0xfdfffffffff00000

def z268 : W := mkw 0x420080156c3add7e 0x68401002ad875baf 0x120000003c7fffff 0x02400000078fffff

def z269 : W := mkw 0x0000801020201024 0x4000100204040204 0x44038c7020007000 0x0880718e04000e00

def z270 : W := mkw 0x09ffffeaa9350007 0x013ffffd5526a000 0xedffffffc03f8000 0xfdbffffff807f000

def z271 : W := mkw 0x4000000556caefd8 0x88000000aad95dfb 0x120000003fffffff 0x0240000007ffffff

def z272 : W := mkw 0x097d3fea80000000 0x012fa7fd50000000 0x0c3c3fffc0000000 0xa18787fff8000000

def z273 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0xb0040f8000407fc7 0xb60081f000080ff8

def z274 : W := mkw 0x00400a0004004800 0x0008014000800900 0xf3c40f803c407fc7 0xbe7881f007880ff8

def z275 : W := mkw 0x03e6ca5c3e785c36 0x607cd94b87cf0b86 0xffffce7c3ff87c3f 0xfffff9cf87ff0f87

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x00007000003f8000 0x40000e000007f000

def z277 : W := mkw 0x016c0f8000000000 0x002d81f000000000 0xe1fc0f8000000000 0xbc3f81f000000000

def z278 : W := mkw 0x09ffffeabb750007 0x013ffffd576ea000 0x47fb8c703f800000 0x08ff718e07f00000

def z279 : W := mkw 0x09bff5a2bb750007 0x0137feb4576ea000 0xe3fff183ffff8007 0x7c7ffe307ffff000

def z280 : W := mkw 0x42c2ca5d6c3add7e 0x6858594bad875baf 0xffc3ce7c3c7fffff 0xdff879cf878fffff

def z281 : W := mkw 0xc400801561aeb77c 0xd8801002ac35d6ef 0x1000000023ffffff 0x02000000047fffff

def z282 : W := mkw 0x09f77aea80000000 0x013eef5d50000000 0x8dc7f2ffc0000000 0x51b8fe5ff8000000

def z283 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xe5fffc7000000000 0x7cbfff8e00000000

def z284 : W := mkw 0x0093f00029350007 0x00127e000526a000 0x0003f000003f8000 0x40007e000007f000

def z285 : W := mkw 0x0082c00428380416 0x0010580085070082 0xfbc3c20c3c380c3b 0xdf78784187870187

def z286 : W := mkw 0x42c24a4d4c1acd5a 0x28584949a98359ab 0xbbc4738fdc7f8fff 0xf7788e71fb8ff1ff

def z287 : W := mkw 0x000080003ff56a87 0x8000100007fead50 0x120000003fffffc7 0x0240000007fffff8

def z288 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0x47fb8c703f807000 0x08ff718e07f00e00

def z289 : W := mkw 0x09ff7fea80802200 0x813feffd50100440 0xfdffffffe3807305 0xffbffffffc700e60

def z290 : W := mkw 0x0000000000000000 0x0000000000000000 0xa004700000000000 0x74008e0000000000

def z291 : W := mkw 0x08592fea80000000 0x010b25fd50000000 0x6c3bafffc0000000 0xed8775fff8000000

def z292 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xe3fc0f803f807000 0xbc7f81f007f00e00

def z293 : W := mkw 0x40192527400a8558 0x080324a4e80150ab 0xfc3fffffc07f8fff 0xff87fffff80ff1ff

def z294 : W := mkw 0x09ff7fea96404880 0x013feffd52c80910 0xefffffffdc400cc2 0xfdfffffffb880198

def z295 : W := mkw 0x0293f05c293d1437 0x60527e0b8527a286 0x0c03f07c003f8038 0x41807e0f8007f007

def z296 : W := mkw 0x02400a5804005820 0x6048014b00800b04 0x04000c7000007000 0x0080018e00000e00

def z297 : W := mkw 0x09e65ac89a510003 0x013ccb59134a2000 0x83c4528cdc598002 0x10788a519b8b3000

def z298 : W := mkw 0x86cacf7f2cba7f3e 0xf0d959efe5974fe7 0xffc3cf7f3c387f3b 0xdff879efe7870fe7

def z299 : W := mkw 0x09e65ac880000000 0x013ccb5910000000 0x01c0000000000000 0x0038000000000000

def z300 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x83fc03801fc00fc6 0x307f807003f801f8

def z301 : W := mkw 0x01b7f0103b751027 0x4036fe02076ea204 0xfffffc703ffff03f 0xffffff8e07fffe07

def z302 : W := mkw 0x856c8f9137e67bac 0xd0ad91f226fccf75 0xf3fc0f803fe67fff 0xbe7f81f007fccfff

def z303 : W := mkw 0x01e65a801e514883 0x003ccb5003ca2910 0x83c452801c598cc2 0x10788a50038b3198

def z304 : W := mkw 0x020080143f7d5c37 0x6040100287efab86 0x120000003ffffc3f 0x0240000007ffff87

def z305 : W := mkw 0x4000000140028148 0x0800000028005029 0x00000183c00003c0 0x0000003078000078

def z306 : W := mkw 0x400080057b7f855f 0x08001000af6ff0ab 0x120000003fff8fff 0x0240000007fff1ff

def z307 : W := mkw 0x41ffff857fffefdf 0x883ffff0affffdfb 0xfbffff8fffffffff 0xff7ffff1ffffffff

def z308 : W := mkw 0x0000001000001020 0x4000000200000204 0x1c000c7000007038 0x8380018e00000e07

def z309 : W := mkw 0x02400a5c04085c30 0x6048014b80810b86 0xbc004e7c00387c3b 0xd78009cf80070f87

def z310 : W := mkw 0x856c0fb316c27ba8 0xd0ad81f662d84f75 0xfffc0ff33fc07fff 0xbfff81fe67f80fff

def z311 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x81fc738fc0000000 0x303f8e71f8000000

def z312 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x53f80c003fc07fc7 0x0a7f018007f80ff8

def z313 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xf3fff3803fff8fc7 0xfe7ffe7007fff1f8

def z314 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x3800238fc0260ffd 0xe7000471f804c1ff

def z315 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x1c03ad7300267338 0xc38075ae6004ce67

def z316 : W := mkw 0x40480f85448aefd8 0x880901f0a8915dfb 0xb8047f8fc07fffff 0xf7008ff1f80fffff

def z317 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x4c3bac7323a67038 0x4987758e6474ce07

def z318 : W := mkw 0x0124000012400000 0x0024800002480000 0x43f800003f800000 0x087f000007f00000

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0xb804738fc0400fc7 0xf7008e71f80801f8

def z320 : W := mkw 0x8659af7f25ae7f3c 0xf0cb35efe4b5cfe7 0x7c3baf7f23a67f3d 0xef8775efe474cfe7

def z321 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x10043183c07f8fff 0x22008630780ff1ff

def z322 : W := mkw 0x00480f0004806a00 0x800901e000900d40 0xf3f80f003f807f07 0xbe7f01e007f00fe0

def z323 : W := mkw 0x0000000013450001 0x000000000268a000 0x0000000003c78004 0x000000000078f000

def z324 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x4dfb8fffc0000000 0x89bf71fff8000000

def z325 : W := mkw 0x4082c005683a855e 0x08105800ad0750ab 0xfbc7f38ffc7f8fff 0xff78fe71ff8ff1ff

def z326 : W := mkw 0x87ffff7f3fff7f3f 0xf0ffffefe7ffefe7 0xffffff7f3fffff3f 0xffffffefe7ffffe7

def z327 : W := mkw 0x8408853321a6332c 0xd08110a66434c665 0x1c000d7323a6733d 0x838001ae6474ce67

def z328 : W := mkw 0x4282c05d683a957e 0x6850580bad0752af 0x0c03f07fc03f8038 0x41807e0ff807f007

def z329 : W := mkw 0x85bff5323bf53227 0xd0b7fea6477ea644 0xe7fffc703ffff007 0x7cffff8e07fffe00

def z330 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43fb80003fff8007 0x087f700007fff000

def z331 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x73f80d003f807305 0xae7f01a007f00e60

def z332 : W := mkw 0x09ff7fea84806a80 0x813feffd50900d50 0xfdffffffc0007fc0 0xffbffffff8000ff8

def z333 : W := mkw 0x0011a01021241024 0x4002340204248204 0x7c3bac7023a6703d 0xef87758e0474ce07

def z334 : W := mkw 0xc419a53761aeb77c 0xd88334a6ec35d6ef 0x7c3bafffe3a67ffd 0xef8775fffc74cfff

def z335 : W := mkw 0x0000000400080410 0x0000000080010082 0xb804738fc0380c3b 0xf7008e71f8070187

def z336 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3ff80003fc00007 0x3c7ff00007f80000

def z337 : W := mkw 0x4000000140028148 0x0800000028005029 0x00000000004783c4 0x000000000008f078

def z338 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004300000478004 0x200086000008f000

def z339 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7fe7c3c7ffc3f 0xfff8ffcf878fff87

def z340 : W := mkw 0xc5bff5377bffb77f 0xd8b7fea6ef7ff6ef 0xffffffffffffffff 0xffffffffffffffff

def z341 : W := mkw 0x012c058012c02280 0x802580b002580450 0xb03c038003c00fc7 0xb6078070007801f8

def z342 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xc5ffdefcc0000000 0x18bffbdf98000000

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0xa004038000000000 0xb400807000000000

def z344 : W := mkw 0x0882504880000000 0x01104a0910000000 0x0000500cc0000000 0x00000a0198000000

def z345 : W := mkw 0x8400000101862308 0x908000002030c461 0x0000000003860304 0x000000000070c060

def z346 : W := mkw 0x41a650045a598453 0x0834ca008b4b308a 0x83c4528cdc598cc2 0x10788a519b8b3198

def z347 : W := mkw 0x01a650001a510003 0x0034ca00034a2000 0x03c000001c000000 0x0078000003800000

def z348 : W := mkw 0x0011a0003b750007 0x00023400076ea000 0x623ba0003fff8007 0x6c47740007fff000

def z349 : W := mkw 0x01ee4fc800000000 0x003dc9f900000000 0xedffcffc00000000 0xfdbff9ff80000000

def z350 : W := mkw 0x093d35a280000000 0x0127a6b450000000 0xa83c738fc0000000 0xf5078e71f8000000

def z351 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fbc0003fb80003 0x5c7f780007f70000

def z352 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x0c3ba17303a6033c 0x6187742e6074c067

def z353 : W := mkw 0x01ffff803ff56a87 0x803ffff007fead50 0xe3fffc003ffff007 0x7c7fff8007fffe00

def z354 : W := mkw 0x4000000440088450 0x080000008801108a 0xb004538cc0598fc7 0xb6008a71980b31f8

def z355 : W := mkw 0x857dafb237e47aa4 0xd0afb5f646fc8f54 0xf7ff8ff03fc07fc7 0xbefff1fe07f80ff8

def z356 : W := mkw 0x0019a50021a42204 0x800334a004348440 0x703bad0023a67305 0xee0775a00474ce60

def z357 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x3800710fc03f833d 0xe7000e21f807f067

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800038fc0000000 0x81000071f8000000

def z359 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x0800000fc0000038 0x01000001f8000007

def z360 : W := mkw 0x8408853320a2332c 0xd08110a664144665 0x7c038d7320207339 0xcf8071ae64040e67

def z361 : W := mkw 0x8693e07f293e153e 0x70d27c0fe527c2a7 0x0c03e07f003e0038 0x41807c0fe007c007

def z362 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x38002103007f8fff 0xe7000420600ff1ff

def z363 : W := mkw 0x0000801020201024 0x4000100204040204 0x0c03807000200038 0x4180700e00040007

def z364 : W := mkw 0x853d25a313c62388 0x90a7a4b46278c471 0x003c218303c603c4 0x200784306078c078

def z365 : W := mkw 0x416c0f8556caefd8 0x882d81f0aad95dfb 0xfbfc0f8fffc07fff 0xbf7f81f1fff80fff

def z366 : W := mkw 0x8dfffffaa1a43224 0xd1bfffff54348644 0xedffffffe3807000 0xfdbffffffc700e00

def z367 : W := mkw 0x0000000004806a80 0x8000000000900d50 0x1000000000007fc0 0x0200000000000ff8

def z368 : W := mkw 0x4000000140028148 0x0800000028005029 0xb0043383c0478fc7 0xb60086707808f1f8

def z369 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x103c0f8003c07fc4 0xa20781f000780ff8

def z370 : W := mkw 0x08400ac880000000 0x0108015910000000 0x0000028cc0000000 0x0000005198000000

def z371 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x5c3b8d7323807338 0x8b8771ae64700e67

def z372 : W := mkw 0x03f7fa4c3f7d4c17 0x207eff4987efa982 0xe3fff20c3fff8c07 0x7c7ffe4187fff180

def z373 : W := mkw 0x093d35a280000000 0x0127a6b450000000 0x003c3183c0000000 0x2007863078000000

def z374 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xf7ff8ff03fc07fc7 0xbefff1fe07f80ff8

def z375 : W := mkw 0x02d3fa5c2d3d5c37 0x605a7f4b85a7ab86 0xffc3fe7c3c3ffc3b 0xdff87fcf8787ff87

def z376 : W := mkw 0x09ffffeaa1240004 0x013ffffd54248000 0xedffffffe3a60005 0xfdbffffffc74c000

def z377 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x4fc3cc7c3c387038 0x49f8798f87870e07

def z378 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000010000000305 0xa600002000000060

def z379 : W := mkw 0x0082400000000000 0x0010480000000000 0xe1c3c00000000000 0x5c38780000000000

def z380 : W := mkw 0x00c24a4c00080410 0x0018494980010082 0xfdc3ce7c00380c3b 0xdfb879cf80070187

def z381 : W := mkw 0x0082c00028300006 0x0010580005060000 0x0003c00000380000 0x4000780000070000

def z382 : W := mkw 0x08ca4fea80000000 0x011949fd50000000 0xedc3cfffc0000000 0xddb879fff8000000

def z383 : W := mkw 0x01ee5f801ed16a83 0x803dcbf003da2d50 0xf3fc5f803fd9ffc7 0xbe7f8bf007fb3ff8

def z384 : W := mkw 0x42c24a4c4c18cc52 0x285849498983198a 0x83c4528cdc598cc2 0x10788a519b8b3198

def z385 : W := mkw 0x01b7f0013b77010f 0x0036fe00276ee021 0xfbfff1033fff833f 0xff7ffe2067fff067

def z386 : W := mkw 0x41b7f0057b7f855f 0x0836fe00af6ff0ab 0xebfff00fffff803f 0x7d7ffe01fffff007

def z387 : W := mkw 0x8411a0332126112c 0x508234066424c225 0x6c3ba07323a6003d 0x6d87740e6474c007

def z388 : W := mkw 0x016c0f8000000000 0x002d81f000000000 0x41f80c0000000000 0x083f018000000000

def z389 : W := mkw 0x02c2ca5c3f7d5c37 0x6058594b87efab86 0xffc3ce7c3ffffc3f 0xdff879cf87ffff87

def z390 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb0047000007f8fff 0x76008e00000ff1ff

def z391 : W := mkw 0x000080112022112c 0x4000100224044225 0x7c03ad732026733d 0xef8075ae6404ce67

def z392 : W := mkw 0x416c0f8556caefd8 0x882d81f0aad95dfb 0xf3fc0f803fffffff 0xbe7f81f007ffffff

def z393 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x8004738fc05f8fc6 0x30008e71f80bf1f8

def z394 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x9004528cc07f8fff 0x12008a51980ff1ff

def z395 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x00000000003f8038 0x000000000007f007

def z396 : W := mkw 0x0282c05c28381436 0x6050580b85070286 0x7c03cc7c20387039 0xcf80798f84070e07

def z397 : W := mkw 0x012c050012c02200 0x802580a002580440 0xf3fc0d003fc07307 0xbe7f81a007f80e60

def z398 : W := mkw 0x4000000440088450 0x080000008801108a 0xb804528cc0798cfb 0xd7008a51980f319f

def z399 : W := mkw 0x85ffffb33ff77baf 0xd0bffff667feef75 0xfffffff33fffffff 0xfffffffe67ffffff

def z400 : W := mkw 0x4000000440088450 0x080000008801108a 0x0000500cc0198000 0x00000a0198033000

def z401 : W := mkw 0x03eecfdc2c385c36 0x607dd9fb85870b86 0xffffcffc3c387c3b 0xfffff9ff87870f87

def z402 : W := mkw 0x0008050100822308 0x800100a020104461 0x78382d0323a6733d 0xef0705a06474ce67

def z403 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb800438fc0380ffb 0xd7000871f80701ff

def z404 : W := mkw 0x096c0fea96c06a80 0x812d81fd52d80d50 0xfffc0fffffc07fc7 0xbfff81fffff80ff8

def z405 : W := mkw 0x4000000440088450 0x080000008801108a 0x0000000000598cc2 0x00000000000b3198

def z406 : W := mkw 0x8619a5372dbe7f3e 0xf0c334a6e5b7cfe7 0x7e3bad733fbe7f3f 0xefc775ae67f7cfe7

def z407 : W := mkw 0x09ee5fc896c06a80 0x813dcbf912d80d50 0xf3fc5f8cffc07fc7 0xbe7f8bf19ff80ff8

def z408 : W := mkw 0x41240005524a8558 0x08248000aa4950ab 0xfbfc738fffff8fff 0xff7f8e71fffff1ff

def z409 : W := mkw 0xc57dafb777eefffc 0xd8afb5f6eefddfff 0xffffffffffffffff 0xffffffffffffffff

def z410 : W := mkw 0x8d3d35a381862308 0x91a7a6b47030c461 0x003c3183c3860304 0x200786307870c060

def z411 : W := mkw 0x41b77005400a8558 0x0836ee00a80150ab 0xf9fff38fc07f8fff 0xff3ffe71f80ff1ff

def z412 : W := mkw 0xc4080537408ab778 0xd88100a6e81156ef 0xbc047fffc07fffff 0xf7808ffff80fffff

def z413 : W := mkw 0x840080112126112c 0x508010022424c225 0x0000000000260038 0x000000000004c007

def z414 : W := mkw 0x016c0f8016404880 0x002d81f002c80910 0xe3fc0f801c400cc2 0xbc7f81f003880198

def z415 : W := mkw 0x0bfffffebef87eb6 0xe17fffffd7df0fd6 0xfffffffffff87fff 0xffffffffffff0fff

def z416 : W := mkw 0x8419252301862308 0x908324a46030c461 0x70382d0323867305 0xae0705a06470ce60

def z417 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0xf7c38e703c007c03 0x9ef871ce07800f80

def z418 : W := mkw 0x012c058012c02280 0x802580b002580450 0xe3fc01803fc003c7 0x3c7f803007f80078

def z419 : W := mkw 0x0019a52221240004 0x000334a444248000 0x6c3bad7323a60005 0xed8775ae6474c000

def z420 : W := mkw 0x01ffff803ff56a87 0x803ffff007fead50 0x43fb8c003f807000 0x087f718007f00e00

def z421 : W := mkw 0x01640a8016404880 0x002c815002c80910 0x03c000001c000000 0x0078000003800000

def z422 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1804338fc0478ffc 0xa3008671f808f1ff

def z423 : W := mkw 0x0019a53220201024 0x400334a644040204 0x7c3bad7320207039 0xef8775ae64040e07

def z424 : W := mkw 0x020000040c184c12 0x2040000081830982 0x020000001c180c02 0x0040000003830180

def z425 : W := mkw 0x01640a8016c06a80 0x802c815002d80d50 0x93c402803fc07fc7 0x1278805007f80ff8

def z426 : W := mkw 0x0135a00033640004 0x0026b400066c8000 0xe3ffa0003fe60007 0x7c7ff40007fcc000

def z427 : W := mkw 0x8400001100823328 0xd080000220104665 0x1000000000007338 0x0200000000000e67

def z428 : W := mkw 0x02408a5c24285c34 0x6048114b84850b86 0x7c038e7c20207c39 0xcf8071cf84040f87

def z429 : W := mkw 0x8400801121a6332c 0xd08010022434c665 0x3800210323a6733d 0xe70004206474ce67

def z430 : W := mkw 0x8411a03321a6332c 0xd08234066434c665 0x1c03a07323a6733d 0x4380740e6474ce67

def z431 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb800420c007f8fff 0xd7000841800ff1ff

def z432 : W := mkw 0x09ffffeabff56a87 0x813ffffd57fead50 0xffffffffffffffc7 0xfffffffffffffff8

def z433 : W := mkw 0x4000000440088450 0x080000008801108a 0xa004728cc07f8cc7 0x74008e51980ff198

def z434 : W := mkw 0x0bfffffebf7d5c37 0x617fffffd7efab86 0xfffffffffffffc3f 0xffffffffffffff87

def z435 : W := mkw 0x41b7f0047b7d8457 0x0836fe008f6fb08a 0xe3fff28cffff8cc7 0x7c7ffe519ffff198

def z436 : W := mkw 0x42400a5d440add78 0x6848014ba8815baf 0x1c000fffc0007ff8 0x838001fff8000fff

def z437 : W := mkw 0x0011a00021240004 0x0002340004248000 0xe03ff00023ff8007 0x7c07fe00047ff000

def z438 : W := mkw 0x0008058000802280 0x800100b000100450 0x00000180000003c0 0x0000003000000078

def z439 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x0804718fc07f83fc 0x61008e31f80ff07f

def z440 : W := mkw 0x0093f00029350007 0x00127e000526a000 0x603bf00023bf8005 0x6c077e000477f000

def z441 : W := mkw 0x03eecfd83ef07aa6 0xe07dd9fb07de0f54 0xf7ff8ff03fc07fc7 0xbefff1fe07f80ff8

def z442 : W := mkw 0x857d2fa317c66b88 0x90afa5f462f8cd71 0xf3fc2f833fc67fc7 0xbe7f85f067f8cff8

def z443 : W := mkw 0x0124100012410001 0x0024820002482000 0x0004100000418000 0x0000820000083000

def z444 : W := mkw 0x0000800021240004 0x0000100004248000 0x0000000023a60005 0x000000000474c000

def z445 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x43fc0d803fc073c4 0x287f81b007f80e78

def z446 : W := mkw 0x016c0f8000802200 0x802d81f000100440 0xf1fc0f8023807305 0xbe3f81f004700e60

def z447 : W := mkw 0x0011a00021240004 0x0002340004248000 0x0003a00000260000 0x400074000004c000

def z448 : W := mkw 0x0000801020201024 0x4000100204040204 0x1000000020207039 0x0200000004040e07

def z449 : W := mkw 0x00db6f6a00000000 0x001b6ded40000000 0xedfbef7f00000000 0xfdbf7defe0000000

def z450 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xc3ffd0003fd98002 0x187ffa0007fb3000

def z451 : W := mkw 0x0008050000802200 0x800100a000100440 0x40380c0023807000 0x0807018004700e00

def z452 : W := mkw 0x853db53333e7332d 0xd0a7b6a6667ce665 0x7c3fbd7323e7f33d 0xef87f7ae647cfe67

def z453 : W := mkw 0x0a480ffe84085c30 0x614901ffd0810b86 0x1c000fffc0007c38 0x838001fff8000f87

def z454 : W := mkw 0xc6dbef7f6dbeff7e 0xf8db7defedb7dfef 0xffffffffffffffff 0xffffffffffffffff

def z455 : W := mkw 0x4000000040008040 0x0800000008001008 0x00041080c04180c0 0x0000821018083018

def z456 : W := mkw 0x08db7fea80000000 0x011b6ffd50000000 0x0c03ffffc0000000 0xc1807ffff8000000

def z457 : W := mkw 0x42c2ca5d6c3add7e 0x6858594bad875baf 0xffc3fe7ffc3ffc3b 0xdff87fcfff87ff87

def z458 : W := mkw 0x49ff7febc0028148 0x093feffd78005029 0xedffffffc04783c4 0xfdbffffff808f078

def z459 : W := mkw 0x0124000000000000 0x0024800000000000 0xe1fc000000000000 0x3c3f800000000000

def z460 : W := mkw 0x8419a5333bf7332f 0xd08334a6677ee665 0x7e3bad733ffff33f 0xefc775ae67fffe67

def z461 : W := mkw 0x01ee4fc816c06a80 0x803dc9f902d80d50 0xffffcffc3fc07fc7 0xfffff9ff87f80ff8

def z462 : W := mkw 0x0000000400080410 0x0000000080010082 0x8000420c00180c02 0x1000084180030180

def z463 : W := mkw 0x869be57f29be373e 0xf0d37cafe537c6e7 0x7c3bed7f23be733d 0xef877dafe477ce67

def z464 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb804738fc0000ff8 0xf7008e71f80001ff

def z465 : W := mkw 0x4000000556caefd8 0x88000000aad95dfb 0xba04738fffffffff 0xf7408e71ffffffff

def z466 : W := mkw 0x01ffff803ff56a87 0x803ffff007fead50 0xf3ff8f803fc07fc7 0xbe7ff1f007f80ff8

def z467 : W := mkw 0x0082c0003b750007 0x00105800076ea000 0xe3c3c0003fff8007 0x5c78780007fff000

def z468 : W := mkw 0x013d358013c52281 0x8027a6b00278a450 0x003c318003c783c4 0x200786300078f078

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0xb0047380007f8fc7 0xf6008e70000ff1f8

def z470 : W := mkw 0x09ffffeaa8300006 0x013ffffd55060000 0xeffffffffc380003 0xfdffffffff870000

def z471 : W := mkw 0x49ff7fefc00a8558 0x093feffdf80150ab 0xfdffffffc0000ff8 0xffbffffff80001ff

def z472 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1000000000000ff8 0x02000000000001ff

def z473 : W := mkw 0x0093f0003b750007 0x00127e00076ea000 0x0203f0003fff8007 0x40407e0007fff000

def z474 : W := mkw 0xcdffffffe1aeb77c 0xd9bffffffc35d6ef 0xfdffffffe3ffffff 0xffbffffffc7fffff

def z475 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x003ff00003ff8004 0x6007fe00007ff000

def z476 : W := mkw 0x00c24a4800000000 0x0018494900000000 0x81c0420c00000000 0x1038084180000000

def z477 : W := mkw 0x00400a0404084c10 0x0008014080810982 0xfbc04e0c3c387c3b 0xdf7809c187870f87

def z478 : W := mkw 0x0082c00028300006 0x0010580005060000 0xe3c7f0003c7f8007 0x7c78fe00078ff000

def z479 : W := mkw 0x857dafb337e67bac 0xd0afb5f666fccf75 0x7ffbad733fa6733d 0xefff75ae67f4ce67

def z480 : W := mkw 0x01eecf803ef06a86 0x803dd9f007de0d50 0xf3ffcf803ff87fc7 0xfe7ff9f007ff0ff8

def z481 : W := mkw 0x400080057b7f855f 0x08001000af6ff0ab 0xba04738fffff8fff 0xf7408e71fffff1ff

def z482 : W := mkw 0x4093f005693f855f 0x08127e00ad27f0ab 0xb807f38fc07f8fff 0xf700fe71f80ff1ff

def z483 : W := mkw 0x4000000140028148 0x0800000028005029 0xa804738fc04783c4 0xf5008e71f808f078

def z484 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x45ffbdf3c0000000 0x28bff7be78000000

def z485 : W := mkw 0x40008015602a957c 0x48001002ac0552af 0xfc07ffffe07fffff 0xff80fffffc0fffff

def z486 : W := mkw 0x0011a00021240004 0x0002340004248000 0x403b800023800000 0x0807700004700000

def z487 : W := mkw 0x0bff7ffe84085c30 0x617fefffd0810b86 0xfdffffffc0007c38 0xffbffffff8000f87

def z488 : W := mkw 0x0000000016c06a80 0x8000000002d80d50 0x020000003f807000 0x0040000007f00e00

def z489 : W := mkw 0x0124000012400000 0x0024800002480000 0xf3fc03803fc00fc7 0xbe7f807007f801f8

def z490 : W := mkw 0x8419a53721ae373c 0xd08334a6e435c6e7 0xfc3bef7f23be7f3f 0xff877defe477cfe7

def z491 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x0403807000000000 0x0080700e00000000

def z492 : W := mkw 0x02d3ea5c2d3c5c36 0x605a7d4b85a78b86 0xfffbee7c3fbe7c3f 0xffff7dcf87f7cf87

def z493 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb0040380007f8fff 0xb6008070000ff1ff

def z494 : W := mkw 0x0011200001040000 0x0002240000208000 0x0038200003860004 0x200704000070c000

def z495 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xb800720fc03f8c3b 0xd7000e41f807f187

def z496 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x9804538fc0598ffa 0x93008a71f80b31ff

def z497 : W := mkw 0x4893706fc00a8558 0x09126e0df80150ab 0x0c03f07fc03f8038 0x41807e0ff807f007

def z498 : W := mkw 0x48480fefc00a8558 0x090901fdf80150ab 0x1c000fffc0000ff8 0x838001fff80001ff

def z499 : W := mkw 0x00400a0000000000 0x0008014000000000 0xe1c00e0000000000 0x9c3801c000000000

def z500 : W := mkw 0x097d3fa280000000 0x012fa7f450000000 0xe1fc3f83c0000000 0xbc3f87f078000000

def z501 : W := mkw 0x8400801021a43224 0xd080100204348644 0x0000000023807000 0x0000000004700e00

def z502 : W := mkw 0x0008050016c06a80 0x800100a002d80d50 0x72380d003fc07fc7 0xae4701a007f80ff8

def z503 : W := mkw 0x4000000440088450 0x080000008801108a 0x0000028cc0000cc0 0x0000005198000198

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000038000000fc0 0x82000070000001f8

def z505 : W := mkw 0x02cacfdc2cb87eb6 0xe05959fb85970fd6 0xffc3cffc3c387ffb 0xdff879ff87870fff

def z506 : W := mkw 0x0893f06aa9350007 0x01127e0d5526a000 0x0c03f07fc03f8000 0x41807e0ff807f000

def z507 : W := mkw 0xc400801561aeb77c 0xd8801002ac35d6ef 0xb804738fe3ffffff 0xf7008e71fc7fffff

def z508 : W := mkw 0x0019252200000000 0x000324a440000000 0xec3fffffc0000000 0xfd87fffff8000000

def z509 : W := mkw 0x0008050000802200 0x800100a000100440 0x0038010003800304 0x2007002000700060

def z510 : W := mkw 0x8411a01121a6332c 0xd08234022434c665 0x703ba00023a6733d 0x6e0774000474ce67

def z511 : W := mkw 0x09ee5fea80000000 0x013dcbfd50000000 0x8dc45fffc0000000 0x91b88bfff8000000

def z512 : W := mkw 0x493d35a3c0028148 0x0927a6b478005029 0x003c3183c04783c4 0x200786307808f078

def z513 : W := mkw 0x016c0f8116c26b88 0x802d81f022d84d71 0xfbfc2f833fe67fff 0xff7f85f067fccfff

def z514 : W := mkw 0x093d35a280000000 0x0127a6b450000000 0x6c3fbdf3c0000000 0xed87f7be78000000

def z515 : W := mkw 0x01b770001a510003 0x0036ee00034a2000 0xe3fff0001c598002 0x7c7ffe00038b3000

def z516 : W := mkw 0x0082c00028300006 0x0010580005060000 0x43c380003c000000 0x0878700007800000

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0xa800420c00000000 0xd500084180000000

def z518 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedfbce7c00000000 0xddbf79cf80000000

def z519 : W := mkw 0x01640a8016404880 0x002c815002c80910 0xf3c40e803c407cc3 0x9e7881d007880f98

def z520 : W := mkw 0x0000800028300006 0x0000100005060000 0x020000003c380003 0x0040000007870000

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000400000380003 0x5400080000070000

def z522 : W := mkw 0x420080156c3add7e 0x68401002ad875baf 0xba04738ffc7fffff 0xf7408e71ff8fffff

def z523 : W := mkw 0x0282c05c28381436 0x6050580b85070286 0xefc3c07c3c38003b 0x5df8780f87870007

def z524 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xe3fc0c003fc07007 0x3c7f818007f80e00

def z525 : W := mkw 0x0093700000000000 0x00126e0000000000 0x0003f00000000000 0x40007e0000000000

def z526 : W := mkw 0x01640a8000000000 0x002c815000000000 0x81c4028000000000 0x1038805000000000

def z527 : W := mkw 0x8dfffffba126112c 0x51bfffff7424c225 0xedffffffc0260038 0xfdbffffff804c007

def z528 : W := mkw 0x08480fea80000000 0x010901fd50000000 0xac047fffc0000000 0xf5808ffff8000000

def z529 : W := mkw 0x012c058016c06a80 0x802580b002d80d50 0x123c01803fc07fc7 0x2247803007f80ff8

def z530 : W := mkw 0x8408053300823328 0xd08100a660104665 0x3c002d730026733d 0xe78005ae6004ce67

def z531 : W := mkw 0x03b7f05c3b7d1437 0x6076fe0b876fa286 0xeffff07c3fff803f 0x7dfffe0f87fff007

def z532 : W := mkw 0x09fffffaa0201024 0x413fffff54040204 0xfdffffffe0207039 0xffbffffffc040e07

def z533 : W := mkw 0x02400a5c04085c30 0x6048014b80810b86 0xffc00e7c3c007c3b 0x9ff801cf87800f87

def z534 : W := mkw 0x03f7fa583f755827 0x607eff4b07eeab04 0x47fb8c703f807000 0x08ff718e07f00e00

def z535 : W := mkw 0x853d352313c72309 0x90a7a6a46278e461 0x003c310303c78304 0x200786206078f060

def z536 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0xefc3ce7c3c007000 0xddf879cf87800e00

def z537 : W := mkw 0x8419253301863328 0xd08324a66030c665 0x1c382d730386733c 0xa38705ae6070ce67

def z538 : W := mkw 0x09bf75a280000000 0x0137eeb450000000 0xe1fff183c0000000 0x7c3ffe3078000000

def z539 : W := mkw 0x8dfffffba1a6332c 0xd1bfffff7434c665 0x7dfbad7323a6733d 0xefbf75ae6474ce67

def z540 : W := mkw 0x41b7f0017b77814f 0x0836fe002f6ef029 0xe3fff183ffff83c7 0x7c7ffe307ffff078

def z541 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x93c0420c3c387c3b 0x1278084187870f87

def z542 : W := mkw 0x4000000440088450 0x080000008801108a 0xa804738fc0598cc2 0xf5008e71f80b3198

def z543 : W := mkw 0x02dbef7e2c385c36 0x605b7defc5870b86 0xfffbef7f3c387c3b 0xffff7defe7870f87

def z544 : W := mkw 0x0135300013450001 0x0026a6000268a000 0xe3fc30003fc78007 0x3c7f860007f8f000

def z545 : W := mkw 0x0282c05c2c385c36 0x6050580b85870b86 0x1e03c07c3c387c3b 0x43c0780f87870f87

def z546 : W := mkw 0x016c0f8000000000 0x002d81f000000000 0xe9fc7f8fc0000000 0xfd3f8ff1f8000000

def z547 : W := mkw 0x0135b0003b750007 0x0026b600076ea000 0x023c30003fff8007 0x2047860007fff000

def z548 : W := mkw 0x0135300013450001 0x0026a6000268a000 0xa03c700003ff8007 0x74078e00007ff000

def z549 : W := mkw 0x016c0f8000000000 0x002d81f000000000 0xf1fc0f8000400fc7 0xbe3f81f0000801f8

def z550 : W := mkw 0x01b7700012400000 0x0036ee0002480000 0xe3fff0003fc00007 0x7c7ffe0007f80000

def z551 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3f80e003f807c03 0x9e7f01c007f00f80

def z552 : W := mkw 0x8411202301060108 0x108224046020c021 0x0000200300060000 0x000004006000c000

def z553 : W := mkw 0x02c2ca5c28381436 0x6058594b85070286 0xedc3ce7c00380038 0xddb879cf80070007

def z554 : W := mkw 0x01bf752200000000 0x0037eea440000000 0xedfffd7300000000 0xfdbfffae60000000

def z555 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0x70380f8023807fc5 0xae0701f004700ff8

def z556 : W := mkw 0x03b7f0143f7d5c37 0x6076fe0287efab86 0xf3fff0003ffffc3f 0x7e7ffe0007ffff87

def z557 : W := mkw 0x4000000140028148 0x0800000028005029 0x00003003c0078000 0x000006007800f000

def z558 : W := mkw 0x41353005534f8559 0x0826a600aa69f0ab 0xb83c738fc3ff8fff 0xf7078e71f87ff1ff

def z559 : W := mkw 0x000000001a510003 0x00000000034a2000 0x020000001c598002 0x00400000038b3000

def z560 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0xe7c3cc703c387003 0x5cf8798e07870e00

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x00043183c0000000 0x2000863078000000

def z562 : W := mkw 0x00000005000a0518 0x00000000a00140a3 0xb800630f003e0f3f 0xf7000c61e007c1e7

def z563 : W := mkw 0x00400a0004004800 0x0008014000800900 0x83c002001c000c02 0x1078004003800180

def z564 : W := mkw 0x0008050000802200 0x800100a000100440 0x10000d0000007300 0x820001a000000e60

def z565 : W := mkw 0x0000800029350007 0x000010000526a000 0x00000000003f8000 0x000000000007f000

def z566 : W := mkw 0x0bfffffea8381436 0x617fffffd5070286 0xedffffffc0380038 0xfdbffffff8070007

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000007f8007 0x00000000000ff000

def z568 : W := mkw 0x85bff5333bf7332f 0xd0b7fea6677ee665 0x7ffbad733fa6733d 0xefff75ae67f4ce67

def z569 : W := mkw 0x017d2fa216c06a80 0x802fa5f442d80d50 0xffffaff33fc07fc7 0xfffff5fe67f80ff8

def z570 : W := mkw 0x0000000000000000 0x0000000000000000 0xa004000000400007 0x3400800000080000

def z571 : W := mkw 0x093d35a293450001 0x0127a6b45268a000 0x003c3183c3c78004 0x200786307878f000

def z572 : W := mkw 0x8419253300823328 0xd08324a660104665 0x7c3bad7300007338 0xef8775ae60000e67

def z573 : W := mkw 0x03ee4fcc1ed86e92 0xa07dc9f983db0dd2 0xf3fc4f8c3fd87fc7 0xbe7f89f187fb0ff8

def z574 : W := mkw 0x01b7700000000000 0x0036ee0000000000 0x41fb800000000000 0x083f700000000000

def z575 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0x7c3fbdf3e3e7f3fd 0xef87f7be7c7cfe7f

def z576 : W := mkw 0x49ff7feec0088450 0x093feffdd801108a 0xedffffffc0598cc2 0xfdbffffff80b3198

def z577 : W := mkw 0x093d35a280000000 0x0127a6b450000000 0x0038000000000000 0x0007000000000000

def z578 : W := mkw 0x0282c05828301026 0x6050580b05060204 0x0403807000000000 0x0080700e00000000

def z579 : W := mkw 0x42c2ca5d6c3add7e 0x6858594bad875baf 0xffc3cffffc387ffb 0xdff879ffff870fff

def z580 : W := mkw 0x8c480ffb80823328 0xd18901ff70104665 0x1c000fffc0007338 0x838001fff8000e67

def z581 : W := mkw 0x412c058552caa7d8 0x882580b0aa5954fb 0xb83c738fc3ff8fff 0xf7078e71f87ff1ff

def z582 : W := mkw 0x093d35a292c02280 0x8127a6b452580450 0x003c3183c3c003c4 0x2007863078780078

def z583 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x8804728fc07f8cfa 0x51008e51f80ff19f

def z584 : W := mkw 0x00480f8016c06a80 0x800901f002d80d50 0x12000f803fc07fc7 0x824001f007f80ff8

def z585 : W := mkw 0x0282c05c28381436 0x6050580b85070286 0xbc03c27c00380c3b 0xd780784f80070187

def z586 : W := mkw 0x02408a5c2c385c36 0x6048114b85870b86 0x1e000e7c3c387c3b 0x83c001cf87870f87

def z587 : W := mkw 0x0011a0012126010c 0x000234002424c021 0x783ba10323a6033d 0xef0774206474c067

def z588 : W := mkw 0x0008851020a03224 0xc00110a204140644 0x7c3b8d7023a0733d 0xef8771ae04740e67

def z589 : W := mkw 0x0000000012c02280 0x8000000002580450 0x0000000003c003c4 0x0000000000780078

def z590 : W := mkw 0x017d3f8017c56a81 0x802fa7f002f8ad50 0xf3fc3f803fc7ffc7 0xbe7f87f007f8fff8

def z591 : W := mkw 0x01640a8016404880 0x002c815002c80910 0xb3c403801c400fc7 0xb6788070038801f8

def z592 : W := mkw 0x01bff5223b750007 0x0037fea4476ea000 0xeffffd733fff8007 0xfdffffae67fff000

def z593 : W := mkw 0x853da53333e6332c 0xd0a7b4a6667cc665 0xffffad733fe6733f 0xfffff5ae67fcce67

def z594 : W := mkw 0x43f7fa5d7f7fdd7f 0x687eff4bafeffbaf 0xffffffffffffffff 0xffffffffffffffff

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0xb000020000000c03 0x9600004000000180

def z596 : W := mkw 0x0000000016404880 0x0000000002c80910 0x020000001c400cc2 0x0040000003880198

def z597 : W := mkw 0x857dafb321a6332c 0xd0afb5f66434c665 0xfdffaff323a6733d 0xffbff5fe6474ce67

def z598 : W := mkw 0x0135300013450001 0x0026a6000268a000 0x0038000003800000 0x0007000000700000

def z599 : W := mkw 0x00c24a4800000000 0x0018494900000000 0x45c38c7000000000 0x08b8718e00000000

def z600 : W := mkw 0x01b7700013450001 0x0036ee000268a000 0xe1fff00003c78004 0x7c3ffe000078f000

def z601 : W := mkw 0x860080152dbe7f3e 0xf0c01002a5b7cfe7 0x120000003fbe7f3f 0x0240000007f7cfe7

def z602 : W := mkw 0x01640a0016404800 0x002c814002c80900 0xf3fc0e003fc07c07 0xbe7f81c007f80f80

def z603 : W := mkw 0x8493f0332937112f 0x50927e066526e225 0x0c03f073003f8038 0x41807e0e6007f007

def z604 : W := mkw 0x49ff7fefc00a8558 0x093feffdf80150ab 0xedffffffc03f8038 0xfdbffffff807f007

def z605 : W := mkw 0x42400a5d440add78 0x6848014ba8815baf 0xbc047fffc07fffff 0xf7808ffff80fffff

def z606 : W := mkw 0x016c0f8004004800 0x002d81f000800900 0xf3fc0f803c007c03 0xbe7f81f007800f80

def z607 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x63fba0003fa60005 0x6c7f740007f4c000

def z608 : W := mkw 0x85b7f0333b77112f 0x50b6fe06676ee225 0xeffff0733fff803f 0x7dfffe0e67fff007

def z609 : W := mkw 0xc411a037612e957c 0x58823406ec25d2af 0x0c03f07fc03f8038 0x41807e0ff807f007

def z610 : W := mkw 0x0019252300020108 0x000324a460004021 0x7c3bad730026033d 0xef8775ae6004c067

def z611 : W := mkw 0x0135300000000000 0x0026a60000000000 0x003c300000000000 0x2007860000000000

def z612 : W := mkw 0x8408053200803220 0xd08100a640100644 0x04000c7000007000 0x0080018e00000e00

def z613 : W := mkw 0x01f77a4800000000 0x003eef4900000000 0xedfffe7c00000000 0xfdbfffcf80000000

def z614 : W := mkw 0x43eecfdd7efafffe 0xe87dd9fbafdf5fff 0xffffffffffffffff 0xffffffffffffffff

def z615 : W := mkw 0x4011a005612e855c 0x08023400ac25d0ab 0xf83ff38fe3ff8fff 0xff07fe71fc7ff1ff

def z616 : W := mkw 0x0008050000802200 0x800100a000100440 0xf03c0f8023c07fc7 0xbe0781f004780ff8

def z617 : W := mkw 0x00400a0004004800 0x0008014000800900 0x10000e0000007c00 0x820001c000000f80

def z618 : W := mkw 0x8fffffffadbe7f3e 0xf1fffffff5b7cfe7 0xffffffffffbe7f3f 0xfffffffffff7cfe7

def z619 : W := mkw 0x01b7f0043b7d0417 0x0036fe00876fa082 0xfbfff20c3fff8c3f 0xff7ffe4187fff187

def z620 : W := mkw 0x03eecfd83ef07aa6 0xe07dd9fb07de0f54 0x47fb8c703f807000 0x08ff718e07f00e00

def z621 : W := mkw 0x01640a8016404880 0x002c815002c80910 0xe3fc02803fc00cc7 0x3c7f805007f80198

def z622 : W := mkw 0x0008052200000000 0x000100a440000000 0x0c000d7300000000 0x818001ae60000000

def z623 : W := mkw 0x02c24a480c104802 0x2058494901820900 0x03c000001c000000 0x0078000003800000

def z624 : W := mkw 0x012c058012c02280 0x802580b002580450 0x703c0d8023c073c5 0xae0781b004780e78

def z625 : W := mkw 0x8dff7feb81862308 0x91bfeffd7030c461 0xedffffffc3860304 0xfdbffffff870c060

def z626 : W := mkw 0x0000000000802200 0x8000000000100440 0x1000000023807305 0x0200000004700e60

def z627 : W := mkw 0x09f77ac880000000 0x013eef5910000000 0xe1fff28cc0000000 0x7c3ffe5198000000

def z628 : W := mkw 0x41640a85564acdd8 0x082c8150aac959bb 0xbbc4738fdc7f8fff 0xf7788e71fb8ff1ff

def z629 : W := mkw 0x0093e00029340006 0x00127c0005268000 0xe3fbe0003fbe0007 0x7c7f7c0007f7c000

def z630 : W := mkw 0x0124000012400000 0x0024800002480000 0x83c400001c400002 0x1078800003880000

def z631 : W := mkw 0x02c24a4c0c184c12 0x2058494981830982 0xbbc0420c1c380c3b 0xd778084183870187

def z632 : W := mkw 0x0000000000000000 0x0000000000000000 0x00040180004003c4 0x2000803000080078

def z633 : W := mkw 0x8411a0332126112c 0x508234066424c225 0x3c03a1730026033d 0xe780742e6004c067

def z634 : W := mkw 0x02cacf5c2cb87e36 0xe05959eb85970fc6 0xfffbcf7c3fb87f3f 0xffff79ef87f70fe7

def z635 : W := mkw 0x0000000100020108 0x0000000020004021 0x100000000026033d 0x020000000004c067

def z636 : W := mkw 0x4282c05d683a957e 0x6850580bad0752af 0xbc07f3ffc07f8fff 0xf780fe7ff80ff1ff

def z637 : W := mkw 0x8419252301862308 0x908324a46030c461 0x6c3bad7303860304 0xed8775ae6070c060

def z638 : W := mkw 0x0000801420281434 0x4000100284050286 0xfc03ce7c20387c3b 0xdf8079cf84070f87

def z639 : W := mkw 0x0000000100020108 0x0000000020004021 0x0800200300260038 0x410004006004c007

def z640 : W := mkw 0x00400a8004004880 0x0008015000800910 0x0000028000000cc0 0x0000005000000198

def z641 : W := mkw 0x01a650001a510003 0x0034ca00034a2000 0xe3fc50003fd98007 0x3c7f8a0007fb3000

def z642 : W := mkw 0x01a6500000000000 0x0034ca0000000000 0x81c4500000000000 0x10388a0000000000

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004500000598002 0x10008a00000b3000

def z644 : W := mkw 0x0082500008110003 0x00104a0001022000 0x0000500000198000 0x00000a0000033000

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x6c038c7000000000 0xcd80718e00000000

def z646 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x6c3bad7323807000 0xed8775ae64700e00

def z647 : W := mkw 0x01f7fa483b750007 0x003eff49076ea000 0xeffffe7c3fff8007 0xfdffffcf87fff000

def z648 : W := mkw 0x00c2ca5820201024 0x4018594b04040204 0xfdc3ce7c20207039 0xdfb879cf84040e07

def z649 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1800738fc03f8ff8 0xc3000e71f807f1ff

def z650 : W := mkw 0x01b7700000000000 0x0036ee0000000000 0xe9fff38fc0000000 0xfd3ffe71f8000000

def z651 : W := mkw 0x0000000016c06a80 0x8000000002d80d50 0xb20403803fc07fc7 0xb640807007f80ff8

def z652 : W := mkw 0x8c93f07ba126112c 0x51927e0f7424c225 0x0c03f07fc0260038 0x41807e0ff804c007

def z653 : W := mkw 0x09ff7feb80020108 0x013feffd70004021 0xfdffffffc026033d 0xffbffffff804c067

def z654 : W := mkw 0x0bfffffaac305826 0x617fffff55860b04 0x47fb8c703c007000 0x08ff718e07800e00

def z655 : W := mkw 0x01b7700000000000 0x0036ee0000000000 0xe1fff000007f8007 0x7c3ffe00000ff000

def z656 : W := mkw 0x0019252200000000 0x000324a440000000 0x443b8c7000000000 0x0887718e00000000

def z657 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x83c7f0001c7f8002 0x5078fe00038ff000

def z658 : W := mkw 0x02c24a4c0c184c12 0x2058494981830982 0xf3c04e0c3c187c03 0x9e7809c187830f80

def z659 : W := mkw 0x036c8f943ef87eb6 0xe06d91f287df0fd6 0xf3fc0f803ff87fff 0xbe7f81f007ff0fff

def z660 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xc3fc0e803fc07cc2 0x187f81d007f80f98

def z661 : W := mkw 0x0000000400080410 0x0000000080010082 0x0800400c00380038 0x4100080180070007

def z662 : W := mkw 0x40080505408aa758 0x880100a0a81154eb 0xf83c7f8fe3ffffff 0xff078ff1fc7fffff

def z663 : W := mkw 0x8c59affba1a6332c 0xd18b35ff7434c665 0x7c3bafffe3a6733d 0xef8775fffc74ce67

def z664 : W := mkw 0x48480fefc00a8558 0x090901fdf80150ab 0xbc047fffc07f8fff 0xf7808ffff80ff1ff

def z665 : W := mkw 0x01b7f00028300006 0x0036fe0005060000 0xe3fff0003c380003 0x7c7ffe0007870000

def z666 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x443bad7323867304 0x288775ae6470ce60

def z667 : W := mkw 0x8419252301862308 0x908324a46030c461 0x3838210303a6033d 0xe70704206074c067

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0xe3c000003c000003 0x1c78000007800000

def z669 : W := mkw 0x017d2fa200000000 0x002fa5f440000000 0xedffaff300000000 0xfdbff5fe60000000

def z670 : W := mkw 0x016c0f8012400000 0x002d81f002480000 0xe3fc0f803fc00007 0xbc7f81f007f80000

def z671 : W := mkw 0xc419a53761aeb77c 0xd88334a6ec35d6ef 0x7c3bad7323ffffff 0xef8775ae647fffff

def z672 : W := mkw 0x0282c0142c385c36 0x6050580285870b86 0xf3c3c0003c387c3b 0x5e78780007870f87

def z673 : W := mkw 0x86dbef7b2db67b2e 0xf0db7def65b6cf65 0x7ffbad733fa6733d 0xefff75ae67f4ce67

def z674 : W := mkw 0x09e65ac880000000 0x013ccb5910000000 0xedc7defcc0000000 0xddb8fbdf98000000

def z675 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1800700fc07f8fff 0x43000e01f80ff1ff

def z676 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xa804738fc03f8038 0xf5008e71f807f007

def z677 : W := mkw 0x02c24a5c04085c30 0x6058494b80810b86 0xfdc3ce7c00007c38 0xdfb879cf80000f87

def z678 : W := mkw 0x02c2ca4c2c384c16 0x2058594985870982 0xe3c3c20c3c380c03 0x5c78784187870180

def z679 : W := mkw 0x85bff53321a6332c 0xd0b7fea66434c665 0xfdfffd7323a6733d 0xffbfffae6474ce67

def z680 : W := mkw 0x02c24a5c0c185c32 0x6058494b81830b86 0x9fc04e7c1c187c3a 0x93f809cf83830f87

def z681 : W := mkw 0x0000000400080410 0x0000000080010082 0xb804720c007f8c3f 0xf7008e41800ff187

def z682 : W := mkw 0x41b7f0057b7f855f 0x0836fe00af6ff0ab 0xf3fff0003fff8fff 0x7e7ffe0007fff1ff

def z683 : W := mkw 0x08480fea84806a80 0x810901fd50900d50 0x1c000fffc0007fc0 0x838001fff8000ff8

def z684 : W := mkw 0x09ee5fc880000000 0x013dcbf910000000 0xe1fc5f8cc0000000 0xbc3f8bf198000000

def z685 : W := mkw 0x0200005c00081430 0x6040000b80010286 0x0c00007c00000038 0x0180000f80000007

def z686 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0x00000c0000007000 0x0000018000000e00

def z687 : W := mkw 0x00400a0004004800 0x0008014000800900 0x43c00c003c007000 0x0878018007800e00

def z688 : W := mkw 0x01a6c0003a700006 0x0034d800074e0000 0xe3ffc0003ff80007 0x7c7ff80007ff0000

def z689 : W := mkw 0x853da5b333e633ac 0xd0a7b4b6667cc675 0x7c3fadf323e673fd 0xef87f5be647cce7f

def z690 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43ffb0003fc78004 0x287ff60007f8f000

def z691 : W := mkw 0x849bf53329b7332f 0xd0937ea66536e665 0x7c3bfd7323bff33d 0xef877fae6477fe67

def z692 : W := mkw 0x0093f00029350007 0x00127e000526a000 0xe3c3f0003c3f8003 0x5c787e000787f000

def z693 : W := mkw 0x020080102c305826 0x6040100205860b04 0x020000003c007000 0x0040000007800e00

def z694 : W := mkw 0x8459af3325a67b2c 0xd08b35e664b4cf65 0xfffbaf733fa67f3f 0xffff75ee67f4cfe7

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004028000400cc2 0x1000805000080198

def z696 : W := mkw 0x41640a845648ccd0 0x082c81508ac9199a 0x83c4528cdc598cc2 0x10788a519b8b3198

def z697 : W := mkw 0xc419a53761aeb77c 0xd88334a6ec35d6ef 0x7c3bfd7fe3bff33d 0xef877faffc77fe67

def z698 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x8fc3c27c1c380c3a 0x51f8784f83870187

def z699 : W := mkw 0x8400801121a6332c 0xd08010022434c665 0x7c038c7023a6733d 0xcf80718e0474ce67

def z700 : W := mkw 0x020080142c385c36 0x6040100285870b86 0xba00420c3c387c3b 0xd740084187870f87

def z701 : W := mkw 0x8411a03221241024 0x5082340644248204 0x0403807000000000 0x0080700e00000000

def z702 : W := mkw 0x8408052300822308 0x908100a460104461 0x0000010300000300 0x0000002060000060

def z703 : W := mkw 0x40400a05440acd58 0x08080140a88159ab 0xfbc47f8ffc7fffff 0xff788ff1ff8fffff

def z704 : W := mkw 0x0124008012400080 0x0024801002480010 0x00040080004000c0 0x0000801000080018

def z705 : W := mkw 0x01b7f00029350007 0x0036fe000526a000 0xe1fff000003f8000 0x7c3ffe000007f000

def z706 : W := mkw 0x020080142c385c36 0x6040100285870b86 0x7e038c703c387c3b 0xcfc0718e07870f87

def z707 : W := mkw 0x09ff7fea9a510003 0x013feffd534a2000 0xefffffffffd98007 0xfdfffffffffb3000

def z708 : W := mkw 0x03753a5c174d5c31 0x606ea74b82e9ab86 0x1c3c3e7c03c7fc3c 0xa38787cf8078ff87

def z709 : W := mkw 0x41b7f0057b7f855f 0x0836fe00af6ff0ab 0x5bfb838fff800ff8 0x8b7f7071fff001ff

def z710 : W := mkw 0x09ff7fea9b550003 0x013feffd536aa000 0xefffffffdfdf8006 0xfdfffffffbfbf000

def z711 : W := mkw 0x089b756a80000000 0x01136ead50000000 0x0c3bf17fc0000000 0x61877e2ff8000000

def z712 : W := mkw 0x09ff7fea93c52281 0x813feffd5278a450 0xedffffffc3c783c4 0xfdbffffff878f078

def z713 : W := mkw 0x49e65accd648ccd0 0x093ccb599ac9199a 0x83c4528cdc598cc2 0x10788a519b8b3198

def z714 : W := mkw 0x03e64acc1e584c92 0x207cc95983cb0992 0x83c0420c1c180c02 0x1078084183830180

def z715 : W := mkw 0x8c19a5b3a1a6332c 0xd18334b67434c665 0x7c3badf3e3a6733d 0xef8775be7c74ce67

def z716 : W := mkw 0xc419a53661acb674 0xd88334a6cc3596ce 0xc43fdefce3d9fcc2 0x1887fbdf9c7b3f98

def z717 : W := mkw 0x0082c01428381436 0x4010580285070286 0xffc3ce7c3c387c3b 0xdff879cf87870f87

def z718 : W := mkw 0xc60080156dbeff7e 0xf8c01002adb7dfef 0x120000003fffffff 0x0240000007ffffff

def z719 : W := mkw 0x03aec5dc3af836b6 0xe075d8bb875f06d6 0x0c3fc1fc03f803fc 0x6187f83f807f007f

def z720 : W := mkw 0xc400801561aeb77c 0xd8801002ac35d6ef 0x1000000023bff33d 0x020000000477fe67

def z721 : W := mkw 0x85ae55331ad3332b 0xd0b5caa6635a6665 0x9fc45d731c59f33a 0x93f88bae638b3e67

def z722 : W := mkw 0x08d37a6a80000000 0x011a6f4d50000000 0x0c03fe7fc0000000 0xc1807fcff8000000

def z723 : W := mkw 0x00dbff802db56a87 0x801b7ff005b6ad50 0x1003ff80003fffc0 0xc2007ff00007fff8

def z724 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc3de7cfc39fc3b 0xdff87bcf9f873f87

def z725 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bad7323fff33f 0xef8775ae647ffe67

def z726 : W := mkw 0x0124000016c06a80 0x8024800002d80d50 0xf3fc03803fc07fc7 0xbe7f807007f80ff8

def z727 : W := mkw 0x096c0fea96c06a80 0x812d81fd52d80d50 0xfffc7fffffc07fc7 0xffff8ffffff80ff8

def z728 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x8c07f2ffc0000000 0x5180fe5ff8000000

def z729 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0xffc38e703c207c3b 0xdff871ce07840f87

def z730 : W := mkw 0x49ff7fefc00a8558 0x093feffdf80150ab 0x55fb8c70007f8fff 0x0abf718e000ff1ff

def z731 : W := mkw 0x09ff7fea84004800 0x013feffd50800900 0xfdffffffc0007c00 0xffbffffff8000f80

def z732 : W := mkw 0x08db7fea80000000 0x011b6ffd50000000 0xac07ffffc0000000 0xf580fffff8000000

def z733 : W := mkw 0x0819256a80000000 0x010324ad50000000 0x6c3bad7fc0000000 0xed8775aff8000000

def z734 : W := mkw 0x09ff7fea9ed16a83 0x813feffd53da2d50 0xffffffffffd9ffc7 0xfffffffffffb3ff8

def z735 : W := mkw 0x09ff7fea92400000 0x013feffd52480000 0xefffffffffff8007 0xfdfffffffffff000

def z736 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc3f803fc7ffc7 0xbe7f87f007f8fff8

def z737 : W := mkw 0x09ff7fea84806a80 0x813feffd50900d50 0xedffffffc0007000 0xfdbffffff8000e00

def z738 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedfbfe7fc0000000 0xddbf7fcff8000000

def z739 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x0c03f3ffc0000000 0xc1807e7ff8000000

def z740 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3baf7323a67f3f 0xff8775ee6474cfe7

def z741 : W := mkw 0x09bf75ea80000000 0x0137eebd50000000 0xac3ff3ffc0000000 0xf587fe7ff8000000

def z742 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bad7323e67fff 0xef8775ae647ccfff

def z743 : W := mkw 0x03b7f0583b751027 0x6076fe0b076ea204 0xe7fff0703fff8007 0x7cfffe0e07fff000

def z744 : W := mkw 0x02c2ca5c2d3d5c37 0x6058594b85a7ab86 0xffc3ce7c3c3ffc3b 0xdff879cf8787ff87

def z745 : W := mkw 0x85b7f0323b751027 0x50b6fe06476ea204 0xe7fff0703fff8007 0x7cfffe0e07fff000

def z746 : W := mkw 0x09ff7fea84004800 0x013feffd50800900 0xfffffffffc407fc7 0xffffffffff880ff8

def z747 : W := mkw 0x08db7fea80000000 0x011b6ffd50000000 0xedc3ffffc0000000 0xddb87ffff8000000

def z748 : W := mkw 0x09ff7fea88110003 0x013feffd51022000 0xedffffffc0198000 0xfdbffffff8033000

def z749 : W := mkw 0x09b7f022bb750007 0x0136fe04576ea000 0xe3fff003ffff8007 0x7c7ffe007ffff000

def z750 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0xfc3fbff3e3e7ffff 0xff87f7fe7c7cffff

def z751 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xcfc3ce7c3c387c3a 0x59f879cf87870f87

def z752 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0x5fc38c703c007038 0x8bf8718e07800e07

def z753 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x7fc38e7c3c207c39 0xcff871cf87840f87

def z754 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7ce7c3c787c3f 0xfff8f9cf878f0f87

def z755 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3fbdf3e3a6733d 0xef87f7be7c74ce67

def z756 : W := mkw 0x8419a53329b7332f 0xd08334a66536e665 0x7c3bad7323bff33d 0xef8775ae6477fe67

def z757 : W := mkw 0x01a6d0003b750007 0x0034da00076ea000 0xe3fc50003fff8007 0x3c7f8a0007fff000

def z758 : W := mkw 0x86db6f6f0d9e6f1a 0xb0db6dede1b3cde3 0x83f8630f1f9e0f06 0x307f0c61e3f3c1e0

def z759 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffc0000fc0 0xffbffffff80001f8

def z760 : W := mkw 0x00480f0016c06a80 0x800901e002d80d50 0xf3f80f003fc07fc7 0xbe7f01e007f80ff8

def z761 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0x4fc38c703c207038 0x49f8718e07840e07

def z762 : W := mkw 0x09ff7fea80802280 0x813feffd50100450 0xedffffffc00003c0 0xfdbffffff8000078

def z763 : W := mkw 0x08db7f6a80000000 0x011b6fed50000000 0xedfbff7fc0000000 0xfdbf7feff8000000

def z764 : W := mkw 0x8419b53321a7332d 0xd08336a66434e665 0x7c3bbd7323a7f33d 0xef8777ae6474fe67

def z765 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xf8047f8fe07fffff 0xff008ff1fc0fffff

def z766 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43fbf0003fff8007 0x487f7e0007fff000

def z767 : W := mkw 0x43e65a4c5e59cc53 0x287ccb498bcb398a 0x83c4528cdc598cc2 0x10788a519b8b3198

def z768 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0400007 0xfdbffffff8080000

def z769 : W := mkw 0x0ac2da5cac385c36 0x61585b4b95870b86 0xffc3de7cfc387c3b 0xdff87bcf9f870f87

def z770 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x4dffbfffc0000000 0xa9bff7fff8000000

def z771 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3ef7f3c387c3b 0xfff87defe7870f87

def z772 : W := mkw 0x09bf75ea80000000 0x0137eebd50000000 0x6c3ffdffc0000000 0xed87ffbff8000000

def z773 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bfd7fe3a6733d 0xef877faffc74ce67

def z774 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x7fc3cc7c3c387039 0xcff8798f87870e07

def z775 : W := mkw 0x00408a1024205824 0x4008114204840b04 0x7fc38c703c207039 0xcff8718e07840e07

def z776 : W := mkw 0xc408851561aeb77c 0xd88110a2ac35d6ef 0xf03c0f8023ffffff 0xbe0781f0047fffff

def z777 : W := mkw 0x02c2cadc2c385cb6 0x6058595b85870b96 0xffc3cefc3c387cfb 0xdff879df87870f9f

def z778 : W := mkw 0x42008015683a957e 0x68401002ad0752af 0x00000000003f8038 0x000000000007f007

def z779 : W := mkw 0x09ff7fea92c02280 0x813feffd52580450 0xfdffffffc3c00fc7 0xffbffffff87801f8

def z780 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xefffffffffc07cc2 0xfdfffffffff80f98

def z781 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bac7323a67039 0xcf87758e6474ce07

def z782 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x0c03807fc0000000 0x0180700ff8000000

def z783 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xfc07ffffc07f8fff 0xff80fffff80ff1ff

def z784 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x443b8c7023a67038 0x0887718e0474ce07

def z785 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xfbfff0003fff803f 0xff7ffe0007fff007

def z786 : W := mkw 0x01b770001b550003 0x0036ee00036aa000 0xa3fc70001fff8007 0x747f8e0003fff000

def z787 : W := mkw 0x0019a51021a43224 0xc00334a204348644 0x7c3bad7023a6733d 0xef8775ae0474ce67

def z788 : W := mkw 0x09b7f06abb750007 0x0136fe0d576ea000 0xe7fff0703fff8007 0x7cfffe0e07fff000

def z789 : W := mkw 0x01b7f0103b751027 0x4036fe02076ea204 0xf3fff0003ffff03f 0x7e7ffe0007fffe07

def z790 : W := mkw 0x0082c01028301026 0x4010580205060204 0x7fc38c703c207039 0xcff8718e07840e07

def z791 : W := mkw 0x42c2ca596c32d96e 0x6858594b2d865b2d 0x47c7bdf3fc47f3c4 0x28f8f7be7f88fe78

def z792 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc0c003fc07fc7 0x3e7f818007f80ff8

def z793 : W := mkw 0x09f77aea80000000 0x013eef5d50000000 0xedfff2ffc0000000 0x7dbffe5ff8000000

def z794 : W := mkw 0x00c24a4804004800 0x0018494900800900 0xffc7fffffc407fc7 0xfff8ffffff880ff8

def z795 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xf7c38e703c387c3b 0x9ef871ce07870f87

def z796 : W := mkw 0x08488feabb750007 0x010911fd576ea000 0x0e000fffffff8007 0x81c001fffffff000

def z797 : W := mkw 0x01b7f0483b750007 0x0036fe09076ea000 0xeffff07c3fff8007 0x7dfffe0f87fff000

def z798 : W := mkw 0x016c0fa216c06a80 0x802d81f442d80d50 0xfffc0ff33fc07fc7 0xbfff81fe67f80ff8

def z799 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7fffc3c7fffff 0xfff8ffff878fffff

def z800 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x53fc0d803fc07fc7 0x2a7f81b007f80ff8

def z801 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x8dfff3ffc0000000 0x71bffe7ff8000000

def z802 : W := mkw 0x0093e0003b750007 0x00127c00076ea000 0xe3fbe0003fff8007 0x7c7f7c0007fff000

def z803 : W := mkw 0x09ff7fea84004800 0x013feffd50800900 0xefffffffdc000c02 0xfdfffffffb800180

def z804 : W := mkw 0x09ee4fea96c06a80 0x813dc9fd52d80d50 0xffffcfffffc07fc7 0xfffff9fffff80ff8

def z805 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bafffe3a6733d 0xef8775fffc74ce67

def z806 : W := mkw 0xc400801577eefffc 0xd8801002aefddfff 0x120000003fffffff 0x0240000007ffffff

def z807 : W := mkw 0x09ff7fea92c02280 0x813feffd52580450 0xfdffffffe3c073c5 0xffbffffffc780e78

def z808 : W := mkw 0x8419253300823328 0xd08324a660104665 0x7c3bad732380733d 0xef8775ae64700e67

def z809 : W := mkw 0x01b7700012400000 0x0036ee0002480000 0xe3fff0003fff8007 0x7c7ffe0007fff000

def z810 : W := mkw 0x097d2fea96c06a80 0x812fa5fd52d80d50 0xffffafffffc07fc7 0xfffff5fffff80ff8

def z811 : W := mkw 0x09e65ac880000000 0x013ccb5910000000 0xedc7ffffc0000000 0xfdb8fffff8000000

def z812 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x6c03fc7fc0000000 0xcd807f8ff8000000

def z813 : W := mkw 0x0082404800000000 0x0010480900000000 0xac07f3ffc0000000 0xf580fe7ff8000000

def z814 : W := mkw 0x0135300013450001 0x0026a6000268a000 0xe3fc70003fff8007 0x7c7f8e0007fff000

def z815 : W := mkw 0x01a6c0003b750007 0x0034d800076ea000 0xe3ffc0003fff8007 0x7c7ff80007fff000

def z816 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x93fc03803fc07fc7 0x327f807007f80ff8

def z817 : W := mkw 0x08db7fea84806a80 0x811b6ffd50900d50 0x1c03ffffc0007fc0 0xc3807ffff8000ff8

def z818 : W := mkw 0x08592fea84806a80 0x810b25fd50900d50 0x7c3bafffe3807fc5 0xef8775fffc700ff8

def z819 : W := mkw 0x8c19b533a1a6332c 0xd18336a67434c665 0x7c3bbd73e3a6733d 0xef8777ae7c74ce67

def z820 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xfbc4738ffc7f8fff 0xff788e71ff8ff1ff

def z821 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x1c3bad7303a6733c 0xe38775ae6074ce67

def z822 : W := mkw 0x097d2fea80000000 0x012fa5fd50000000 0xedffafffc0000000 0xfdbff5fff8000000

def z823 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x543b8c7023807338 0x0a87718e04700e67

def z824 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x743bac7023a6733d 0x6e87758e0474ce67

def z825 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x47c38c703c387038 0x08f8718e07870e07

def z826 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0xf83c738fe3ff8fff 0xff078e71fc7ff1ff

def z827 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc4f803ff87fc7 0xfe7f89f007ff0ff8

def z828 : W := mkw 0x08db7fea80000000 0x011b6ffd50000000 0x0c03fc7fc0000000 0x41807f8ff8000000

def z829 : W := mkw 0x09b7706a80000000 0x0136ee0d50000000 0x8dc7f07fc0000000 0x51b8fe0ff8000000

def z830 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xebfff1033fff8007 0xfd7ffe2067fff000

def z831 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x5c3b8d7323a6733d 0x8b8771ae6474ce67

def z832 : W := mkw 0x09bf75ea80000000 0x0137eebd50000000 0x0c3bf07fc0000000 0x41877e0ff8000000

def z833 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x9fc3ce7c1c387c3a 0xd3f879cf83870f87

def z834 : W := mkw 0x09ff7fea84004800 0x013feffd50800900 0xeffffffffc007000 0xfdffffffff800e00

def z835 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0xbc07f3ffc0400fc7 0xf780fe7ff80801f8

def z836 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7fffffc787fff 0xfff8ffffff8f0fff

def z837 : W := mkw 0x012480003b750007 0x00249000076ea000 0x43f800003fff8007 0x087f000007fff000

def z838 : W := mkw 0x0893706a96c06a80 0x81126e0d52d80d50 0x1e03f07fffc07fc7 0x43c07e0ffff80ff8

def z839 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x4dfffdffc0000000 0x69bfffbff8000000

def z840 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x743b8d7023a6733d 0xae8771ae0474ce67

def z841 : W := mkw 0x02c2ca5c2d3c5c36 0x6058594b85a78b86 0xffc3ce7c3fbe7c3f 0xdff879cf87f7cf87

def z842 : W := mkw 0x8dff7fea81842200 0x91bfeffd50308440 0xedffffffc3800000 0xfdbffffff8700000

def z843 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x5fc3cc7c3c387c3b 0x4bf8798f87870f87

def z844 : W := mkw 0x00408a1424285c34 0x4008114284850b86 0xffc3ce7c3c387c3b 0xdff879cf87870f87

def z845 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffffffffff807fc0 0xfffffffffff00ff8

def z846 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x7fc38c703c387c3b 0xcff8718e07870f87

def z847 : W := mkw 0x02408a142c385c36 0x6048114285870b86 0xffc38e703c387c3b 0xdff871ce07870f87

def z848 : W := mkw 0x09ff7fea96404800 0x013feffd52c80900 0xffffffffffc07c07 0xfffffffffff80f80

def z849 : W := mkw 0x08c24a6a80000000 0x0118494d50000000 0xedc3ce7fc0000000 0xddb879cff8000000

def z850 : W := mkw 0x8d3d35a393c62388 0x91a7a6b47278c471 0x003c3183c3c603c4 0x200786307878c078

def z851 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xefffffffffc07007 0xfdfffffffff80e00

def z852 : W := mkw 0x08592fea80000000 0x010b25fd50000000 0xec3fffffc0000000 0xfd87fffff8000000

def z853 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x543b8c7023a07039 0x0a87718e04740e07

def z854 : W := mkw 0x01b770001b550003 0x0036ee00036aa000 0xe3fff0001fdf8006 0x7c7ffe0003fbf000

def z855 : W := mkw 0x02408a5c24285c34 0x6048114b84850b86 0xffc38e7c3c207c3b 0xdff871cf87840f87

def z856 : W := mkw 0x00c24a4800000000 0x0018494900000000 0xedc3fe7fc0000000 0xddb87fcff8000000

def z857 : W := mkw 0x02c24a5c0c185c32 0x6058494b81830b86 0xffc3ce7c1c187c3a 0xdff879cf83830f87

def z858 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xdfc3ce7c3c187c3a 0x9bf879cf87830f87

def z859 : W := mkw 0x089b756a80802200 0x81136ead50100440 0x7c3bfd7fe3807305 0xef877faffc700e60

def z860 : W := mkw 0x8575aab3376659ac 0x50aeb55666eccb35 0x8fc7a2f31c660cfa 0x51f8f45e638cc19f

def z861 : W := mkw 0x09b7706a9a510003 0x0136ee0d534a2000 0x8fc7f07fdc598002 0x51f8fe0ffb8b3000

def z862 : W := mkw 0x0282c05c28381436 0x6050580b85070286 0xffc3cc7c3c38703b 0xdff8798f87870e07

def z863 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bfd7323bff33d 0xef877fae6477fe67

def z864 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xf3fff2003fff8c07 0xfe7ffe4007fff180

def z865 : W := mkw 0x08db6fea80000000 0x011b6dfd50000000 0xedfbefffc0000000 0xfdbf7dfff8000000

def z866 : W := mkw 0x00c2ca102c305826 0x4018594205860b04 0xffc3ce703c387c3b 0xdff879ce07870f87

def z867 : W := mkw 0x09ff7fea92c02280 0x813feffd52580450 0xedffffffc3800000 0xfdbffffff8700000

def z868 : W := mkw 0x416c0f8556caefd8 0x882d81f0aad95dfb 0x4bf87c0fffbff038 0x497f0f81fff7fe07

def z869 : W := mkw 0x0893706a88110003 0x01126e0d51022000 0x0c03f07fc0198000 0x41807e0ff8033000

def z870 : W := mkw 0x09ff7fea84806a00 0x813feffd50900d40 0xffffffffff807f07 0xfffffffffff00fe0

def z871 : W := mkw 0x097d3fea80000000 0x012fa7fd50000000 0x6c3fbfffc0000000 0xed87f7fff8000000

def z872 : W := mkw 0x0019a53221241024 0x400334a644248204 0x7c3bad7323a6703d 0xef8775ae6474ce07

def z873 : W := mkw 0x0ac2cadcac385c36 0x6158595b95870b86 0xffc3cefcfc387c3b 0xdff879df9f870f87

def z874 : W := mkw 0x09b7f080bb750007 0x0136fe10176ea000 0xe3fff080ffff8007 0x7c7ffe101ffff000

def z875 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x0c07f1ffc0000000 0x6180fe3ff8000000

def z876 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fbf0003fbf8003 0x5c7f7e0007f7f000

def z877 : W := mkw 0x00c24a4c04084c10 0x0018494980810982 0xffc3ce7c3c387c3b 0xdff879cf87870f87

def z878 : W := mkw 0x09ff7fea92400000 0x013feffd52480000 0xffffffffffc00fc7 0xfffffffffff801f8

def z879 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffc07f8fc7 0xffbffffff80ff1f8

def z880 : W := mkw 0x09f77aea96404880 0x013eef5d52c80910 0x8fc7f2ffdc400cc2 0x51f8fe5ffb880198

def z881 : W := mkw 0x09b7f06abb750007 0x0136fe0d576ea000 0xeffff3ffffff8007 0xfdfffe7ffffff000

def z882 : W := mkw 0x0b3db5b6ac385c36 0x6167b6b6d5870b86 0x123c3183fc387c3b 0x224786307f870f87

def z883 : W := mkw 0x09ff7fea92c02280 0x813feffd52580450 0xefffffffffc003c7 0xfdfffffffff80078

def z884 : W := mkw 0x0124000012400000 0x0024800002480000 0xe3fc00003fff8007 0x3c7f800007fff000

def z885 : W := mkw 0xc4008015612e957c 0x58801002ac25d2af 0x00000000003f8038 0x000000000007f007

def z886 : W := mkw 0x09bf75ea80000000 0x0137eebd50000000 0xedfff1ffc0000000 0x7dbffe3ff8000000

def z887 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3ce7c3c7ffc3f 0xdff879cf878fff87

def z888 : W := mkw 0x0093f00029350007 0x00127e000526a000 0xe3fbf0003fbf8007 0x7c7f7e0007f7f000

def z889 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x6dfbafffc0000000 0xedbf75fff8000000

def z890 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xfffbce7c3fb87c3f 0xffff79cf87f70f87

def z891 : W := mkw 0x09f77aea80000000 0x013eef5d50000000 0xedc7feffc0000000 0xddb8ffdff8000000

def z892 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3ce7c3c787fff 0xdff879cf878f0fff

def z893 : W := mkw 0x0019252200000000 0x000324a440000000 0x6c3bfd7fc0000000 0xed877faff8000000

def z894 : W := mkw 0x420080157f7fdd7f 0x68401002afeffbaf 0x120000003fffffff 0x0240000007ffffff

def z895 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc3f83ffc07fc7 0xbe7f87f07ff80ff8

def z896 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff0003fbf8000 0x7c7ffe0007f7f000

def z897 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7cefc3c787cfb 0xdff8f9df878f0f9f

def z898 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x8dc7ffffc0000000 0xd1b8fffff8000000

def z899 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedfbcfffc0000000 0xddbf79fff8000000

def z900 : W := mkw 0x0019252200000000 0x000324a440000000 0x6c3bafffc0000000 0xed8775fff8000000

def z901 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfffbad733fa6733f 0xffff75ae67f4ce67

def z902 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3fad7323e6733f 0xff87f5ae647cce67

def z903 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xeffffc703fff8007 0xfdffff8e07fff000

def z904 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3ffd7323a6733d 0xff87ffae6474ce67

def z905 : W := mkw 0x01b7f0103b751027 0x4036fe02076ea204 0xe7fffc703ffff007 0x7cffff8e07fffe00

def z906 : W := mkw 0x8de6dad9a1a6332c 0xd1bcdb5b3434c665 0x91c4528ce3a6733d 0x12388a519c74ce67

def z907 : W := mkw 0x0000000000000000 0x0000000000000000 0xec07ffffc0000000 0xfd80fffff8000000

def z908 : W := mkw 0x09ff7fea80802200 0x813feffd50100440 0xfdffffffe3c07fc7 0xffbffffffc780ff8

def z909 : W := mkw 0x012480003b750007 0x00249000076ea000 0xe3fc70003fff8007 0x7c7f8e0007fff000

def z910 : W := mkw 0x436c8f957efafffe 0xe86d91f2afdf5fff 0xf3fc0f803fffffff 0xbe7f81f007ffffff

def z911 : W := mkw 0x02c24a5c04085c30 0x6058494b80810b86 0xffc3ce7c3c007c3b 0xdff879cf87800f87

def z912 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffffffffff807305 0xfffffffffff00e60

def z913 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3baff323a67ffd 0xef8775fe6474cfff

def z914 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff2803fff8cc7 0x7c7ffe5007fff198

def z915 : W := mkw 0x01ee4fc816c06a80 0x803dc9f902d80d50 0xffffffffffc07fc7 0xfffffffffff80ff8

def z916 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x1804738fc07f8ffc 0xe3008e71f80ff1ff

def z917 : W := mkw 0x09f77a6a80000000 0x013eef4d50000000 0xedfffe7fc0000000 0xfdbfffcff8000000

def z918 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0xac03f27fc0000000 0xd5807e4ff8000000

def z919 : W := mkw 0x02c2da5c2c395c37 0x60585b4b85872b86 0xffc3de7c3c39fc3b 0xdff87bcf87873f87

def z920 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x4c3bad7323a6733c 0x698775ae6474ce67

def z921 : W := mkw 0x01b7f0223b750007 0x0036fe04476ea000 0xeffff0733fff8007 0x7dfffe0e67fff000

def z922 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xcdffdfffc0000000 0x99bffbfff8000000

def z923 : W := mkw 0x09ff7fea92400000 0x013feffd52480000 0xefffffffdc400002 0xfdfffffffb880000

def z924 : W := mkw 0x0019252300822308 0x800324a460104461 0x7c3bad7323a6733d 0xef8775ae6474ce67

def z925 : W := mkw 0x0135a0003b750007 0x0026b400076ea000 0xe3ffa0003fff8007 0x7c7ff40007fff000

def z926 : W := mkw 0x016c1f8016c16a81 0x802d83f002d82d50 0xf3fc1f803fc1ffc7 0xbe7f83f007f83ff8

def z927 : W := mkw 0x08d37a6a80000000 0x011a6f4d50000000 0xedc7ffffc0000000 0xfdb8fffff8000000

def z928 : W := mkw 0x08db7fea80000000 0x011b6ffd50000000 0x0c038fffc0000000 0x818071fff8000000

def z929 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0xf3f80f803f807fc7 0xbe7f01f007f00ff8

def z930 : W := mkw 0x0093e00029340006 0x00127c0005268000 0xe3fff0003fff8007 0x7c7ffe0007fff000

def z931 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x5fc3ce7c3c387c38 0xcbf879cf87870f87

def z932 : W := mkw 0x08db7fea80000000 0x011b6ffd50000000 0x6c3bffffc0000000 0xed877ffff8000000

def z933 : W := mkw 0x09b7706a80000000 0x0136ee0d50000000 0xedfff3ffc0000000 0xfdbffe7ff8000000

def z934 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc7f803fc07fc7 0xfe7f8ff007f80ff8

def z935 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xfbfc2f833fc07fc7 0xff7f85f067f80ff8

def z936 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x53f80c003f807fc0 0x0a7f018007f00ff8

def z937 : W := mkw 0x853d35a313c72389 0x90a7a6b46278e471 0x003c318303c783c4 0x200786306078f078

def z938 : W := mkw 0x01b770001b550003 0x0036ee00036aa000 0xe3fc70003fdf8007 0x3c7f8e0007fbf000

def z939 : W := mkw 0x853d352313c72309 0x90a7a6a46278e461 0x0038210303860304 0x200704206070c060

def z940 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3fe7c3c3ffc3b 0xdff87fcf8787ff87

def z941 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3fadf323e673fd 0xef87f5be647cce7f

def z942 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7fe7c3c387c3b 0xfff8ffcf87870f87

def z943 : W := mkw 0xc53d352353c7a349 0x98a7a6a46a78f469 0x003c3183c3c783c4 0x200786307878f078

def z944 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffffffffdc407fc2 0xfffffffffb880ff8

def z945 : W := mkw 0x09b7f048bb750007 0x0136fe09176ea000 0xe3fff00cffff8007 0x7c7ffe019ffff000

def z946 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x5c3bac7323a6733d 0x4b87758e6474ce67

def z947 : W := mkw 0x03e65acc1e594c93 0x207ccb5983cb2992 0x83c4528c1c598cc2 0x10788a51838b3198

def z948 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0x7c3bbd73e3a7f33d 0xef8777ae7c74fe67

def z949 : W := mkw 0x0882406a80000000 0x0110480d50000000 0x0c03c07fc0000000 0x4180780ff8000000

def z950 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffc0200039 0xffbffffff8040007

def z951 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3ff80003fff8007 0x3c7ff00007fff000

def z952 : W := mkw 0x0811206a80000000 0x0102240d50000000 0x0c03a07fc0000000 0x4180740ff8000000

def z953 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3b8d7323a07339 0xcf8771ae64740e67

def z954 : W := mkw 0x096c1f8096c06a80 0x812d83f012d80d50 0xf3fc1f80ffc07fc7 0xbe7f83f01ff80ff8

def z955 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc0f803f807fc0 0xbe7f81f007f00ff8

def z956 : W := mkw 0x493d35a3d2c2a3c8 0x8927a6b47a585479 0x003c3183c3c783c4 0x200786307878f078

def z957 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc04003c4 0xfdbffffff8080078

def z958 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3fffffe3fff33f 0xff87fffffc7ffe67

def z959 : W := mkw 0x089b756a80000000 0x01136ead50000000 0x0c03fd7fc0000000 0xc1807faff8000000

def z960 : W := mkw 0x420080157efafffe 0xe8401002afdf5fff 0x120000003fffffff 0x0240000007ffffff

def z961 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffffffffffffffc7 0xfffffffffffffff8

def z962 : W := mkw 0x00c2ca5824205824 0x4018594b04840b04 0xffc3ce7c3c207c3b 0xdff879cf87840f87

def z963 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3bef7f23a6733d 0xff877defe474ce67

def z964 : W := mkw 0x09ff7fea92400000 0x013feffd52480000 0xefffffffff800000 0xfdfffffffff00000

def z965 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3fffffe3e67fff 0xff87fffffc7ccfff

def z966 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0xfc3fffffe3e7f3fd 0xff87fffffc7cfe7f

def z967 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc03f8000 0xfdbffffff807f000

def z968 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xd3fc0e803fc07fc7 0x1a7f81d007f80ff8

def z969 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3b8c7023a6733d 0xcf87718e0474ce67

def z970 : W := mkw 0x8408851121a6332c 0xd08110a22434c665 0x7c3b8d7023a6733d 0xef8771ae0474ce67

def z971 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xebfff00fffff8007 0x7d7ffe01fffff000

def z972 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3fe7ffc387c3b 0xdff87fcfff870f87

def z973 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3ce7c3c007c38 0xdff879cf87800f87

def z974 : W := mkw 0x08d37a6a80000000 0x011a6f4d50000000 0x8dc3f27fc0000000 0x51b87e4ff8000000

def z975 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3cf7c3c387f3f 0xfff879ef87870fe7

def z976 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xfbfc0f803fe07fff 0xff7f81f007fc0fff

def z977 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7cffc3c387c3b 0xfff8f9ff87870f87

def z978 : W := mkw 0x0011a01021241024 0x4002340204248204 0x7c3b8c7023a07039 0xcf87718e04740e07

def z979 : W := mkw 0x09b770ea80000000 0x0136ee1d50000000 0x0c07f0ffc0000000 0x4180fe1ff8000000

def z980 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43fb80003fbf8000 0x087f700007f7f000

def z981 : W := mkw 0x0019252200802200 0x800324a440100440 0xfc3fffffe3c07fc7 0xff87fffffc780ff8

def z982 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x57c38c703c007c38 0x0af8718e07800f87

def z983 : W := mkw 0x01bf752200000000 0x0037eea440000000 0xedffffffc0000000 0xfdbffffff8000000

def z984 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xebfff20c3fff8007 0xfd7ffe4187fff000

def z985 : W := mkw 0x09ff7fea80802200 0x813feffd50100440 0xedffffffe3807000 0xfdbffffffc700e00

def z986 : W := mkw 0x096c0fc896c06a80 0x812d81f912d80d50 0xf3fc0f8cffc07fc7 0xbe7f81f19ff80ff8

def z987 : W := mkw 0x42480fdd448afff8 0xe84901fba8915fff 0x1c000fffc0007ff8 0x838001fff8000fff

def z988 : W := mkw 0xc4008015612e957c 0x58801002ac25d2af 0x10000000007f8fff 0x02000000000ff1ff

def z989 : W := mkw 0x03e65a4c1e594c13 0x207ccb4983cb2982 0x83c0420c1c180c02 0x1078084183830180

def z990 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3b8d732380733d 0xaf8771ae64700e67

def z991 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xc3fff0003fff8002 0x587ffe0007fff000

def z992 : W := mkw 0xc693e07f693e957e 0x78d27c0fed27d2af 0x0c03f07fc03f8038 0x41807e0ff807f007

def z993 : W := mkw 0x0008851020a03224 0xc00110a204140644 0x7c3b8c7023a07039 0xcf87718e04740e07

def z994 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0x7c3badf3e3a673fd 0xef8775be7c74ce7f

def z995 : W := mkw 0x01640a8016c06a80 0x802c815002d80d50 0xf3fc02803fc07fc7 0x3e7f805007f80ff8

def z996 : W := mkw 0x09b7706a80000000 0x0136ee0d50000000 0x0c3ff07fc0000000 0x6187fe0ff8000000

def z997 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xf7c3cc703c387c3b 0x5ef8798e07870f87

def z998 : W := mkw 0x09ff7fea80802200 0x813feffd50100440 0xfdffffffc0007300 0xffbffffff8000e60

def z999 : W := mkw 0x08d37a6a80000000 0x011a6f4d50000000 0x4dc3fc7fc0000000 0x49b87f8ff8000000

def z1000 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xefffffffdfc00fc6 0xfdfffffffbf801f8

def z1001 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x5c3bad7323a67338 0xcb8775ae6474ce67

def z1002 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedfffc7fc0000000 0x7dbfff8ff8000000

def z1003 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x7c3b8d7023a0733d 0xef8771ae04740e67

def z1004 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3fbd7323e7f33d 0xef87f7ae647cfe67

def z1005 : W := mkw 0x09b7706a80000000 0x0136ee0d50000000 0x4dfbf07fc0000000 0x49bf7e0ff8000000

def z1006 : W := mkw 0x08ca4fea80000000 0x011949fd50000000 0x0c03cfffc0000000 0xc18079fff8000000

def z1007 : W := mkw 0x09ff7fea84004880 0x013feffd50800910 0xedffffffc0000cc0 0xfdbffffff8000198

def z1008 : W := mkw 0x08ca4fea84806a80 0x811949fd50900d50 0xffc3cffffc007fc3 0xdff879ffff800ff8

def z1009 : W := mkw 0x0011202200000000 0x0002240440000000 0x0c03f07fc0000000 0x41807e0ff8000000

def z1010 : W := mkw 0x0be65acc9e594c13 0x217ccb5993cb2982 0x83c4528cdc598c02 0x10788a519b8b3180

def z1011 : W := mkw 0x01b7f0103b751027 0x4036fe02076ea204 0xeffff0703fff803f 0x7dfffe0e07fff007

def z1012 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x6dfbfd7fc0000000 0xedbf7faff8000000

def z1013 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc7dffcfc79ffff 0xfff8fbff9f8f3fff

def z1014 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3cffffc387c3b 0xdff879ffff870f87

def z1015 : W := mkw 0x01b7f0803b750087 0x0036fe10076ea010 0xe3fff0803fff80c7 0x7c7ffe1007fff018

def z1016 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x73f80d003fc07fc7 0xae7f01a007f80ff8

def z1017 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0x5ffb8fffff807fc0 0x8bff71fffff00ff8

def z1018 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xffff8ff03fc07fc7 0xfffff1fe07f80ff8

def z1019 : W := mkw 0x01a6c0003a700006 0x0034d800074e0000 0xe3fff0003fff8007 0x7c7ffe0007fff000

def z1020 : W := mkw 0x0011a0112126112c 0x400234022424c225 0x7c3bad7323a6733d 0xef8775ae6474ce67

def z1021 : W := mkw 0x096c0fa296c06a80 0x812d81f452d80d50 0xf3fc0f83ffc07fc7 0xbe7f81f07ff80ff8

def z1022 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xf3fff0003fff8fc7 0x7e7ffe0007fff1f8

def z1023 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xefffffffffc073c4 0xfdfffffffff80e78

def z1024 : W := mkw 0x09bf75ea92c02280 0x8137eebd52580450 0x0c3ff1ffc3c003c4 0x6187fe3ff8780078

def z1025 : W := mkw 0x09ff7fea93450001 0x013feffd5268a000 0xedffffffc3800000 0xfdbffffff8700000

def z1026 : W := mkw 0x09ff7fea92410001 0x013feffd52482000 0xedffffffc0418000 0xfdbffffff8083000

def z1027 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xfbfc4f8c3fc07fc7 0xff7f89f187f80ff8

def z1028 : W := mkw 0x0011202200000000 0x0002240440000000 0xac07f3ffc0000000 0xf580fe7ff8000000

def z1029 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc7fffffc79fcfb 0xfff8ffffff8f3f9f

def z1030 : W := mkw 0x08592fea80000000 0x010b25fd50000000 0x4c3b8fffc0000000 0x898771fff8000000

def z1031 : W := mkw 0x01640a0016c06a80 0x802c814002d80d50 0xf3fc0e003fc07fc7 0xbe7f81c007f80ff8

def z1032 : W := mkw 0x09ff7fea81050001 0x013feffd5020a000 0xedffffffc0078000 0xfdbffffff800f000

def z1033 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xfbfff38fffff8fc7 0xff7ffe71fffff1f8

def z1034 : W := mkw 0x0282c0142c385c36 0x6050580285870b86 0xffc3cc703c387c3b 0xdff8798e07870f87

def z1035 : W := mkw 0x089b756a80000000 0x01136ead50000000 0xec3fffffc0000000 0xfd87fffff8000000

def z1036 : W := mkw 0x0008851120a2332c 0xc00110a224144665 0x7c3bad7323a6733d 0xef8775ae6474ce67

def z1037 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0x4ffbfc7fff807000 0x49ff7f8ffff00e00

def z1038 : W := mkw 0x42408a156c3add7e 0x68481142ad875baf 0xf3c40f803c7fffff 0xbe7881f0078fffff

def z1039 : W := mkw 0x08ca4fea80000000 0x011949fd50000000 0xedc7ffffc0000000 0xfdb8fffff8000000

def z1040 : W := mkw 0x012c050016c06a80 0x802580a002d80d50 0xf3fc0d003fc07fc7 0xbe7f81a007f80ff8

def z1041 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc5f803fd9ffc7 0xbe7f8bf007fb3ff8

def z1042 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x9004738fc07f8fff 0x32008e71f80ff1ff

def z1043 : W := mkw 0x0bff7fea8c104802 0x217feffd51820900 0xefffffffdc000000 0xfdfffffffb800000

def z1044 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0xac07f07fc0000000 0x7580fe0ff8000000

def z1045 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x63fbf0003fbf8005 0x6c7f7e0007f7f000

def z1046 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fbc0003fff8007 0x5c7f780007fff000

def z1047 : W := mkw 0x09ff7fea9a510003 0x013feffd534a2000 0xefffffffdc000000 0xfdfffffffb800000

def z1048 : W := mkw 0x0be65acc9e584c92 0x217ccb5993cb0992 0x83c4528cdc580cc2 0x10788a519b8b0198

def z1049 : W := mkw 0x01a650001a510003 0x0034ca00034a2000 0xe3fc70003fff8007 0x7c7f8e0007fff000

def z1050 : W := mkw 0x09ff7fea96404880 0x013feffd52c80910 0xfffffffffc407cc3 0xffffffffff880f98

def z1051 : W := mkw 0x09ff7fea92400000 0x013feffd52480000 0xedffffffc3c00004 0xfdbffffff8780000

def z1052 : W := mkw 0x09ff7fea9e514883 0x013feffd53ca2910 0xefffffffdc598cc2 0xfdfffffffb8b3198

def z1053 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0xedc3f07fc0000000 0x5db87e0ff8000000

def z1054 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0380003 0xfdbffffff8070000

def z1055 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x2c03f17fc0000000 0xe5807e2ff8000000

def z1056 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3ffff323ffffff 0xff87fffe647fffff

def z1057 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3f80f803f807fc3 0x9e7f01f007f00ff8

def z1058 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xeffffffffc000003 0xfdffffffff800000

def z1059 : W := mkw 0x48480fefc48aefd8 0x890901fdf8915dfb 0x1c000fffc0007ff8 0x838001fff8000fff

def z1060 : W := mkw 0x8419a53329b6332e 0xd08334a66536c665 0x7e3bad733fbe733f 0xefc775ae67f7ce67

def z1061 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x5c3bad732386733c 0xab8775ae6470ce67

def z1062 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xd3fc0f803fc07fc2 0x9a7f81f007f80ff8

def z1063 : W := mkw 0x09ff7fea81040000 0x013feffd50208000 0xedffffffc3860004 0xfdbffffff870c000

def z1064 : W := mkw 0x42008015683a957e 0x68401002ad0752af 0x10000000007f8fff 0x02000000000ff1ff

def z1065 : W := mkw 0x41240005524a8558 0x08248000aa4950ab 0xfbfc038fffc00fff 0xbf7f8071fff801ff

def z1066 : W := mkw 0x093d35a280000000 0x0127a6b450000000 0xec3fffffc0000000 0xfd87fffff8000000

def z1067 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3faff323a6733d 0xff87f5fe6474ce67

def z1068 : W := mkw 0x43e64acc5e58ccd2 0x287cc9598bcb199a 0x83c4528cdc598cc2 0x10788a519b8b3198

def z1069 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xfdffffffc3c07fc4 0xffbffffff8780ff8

def z1070 : W := mkw 0x09ee5fea80000000 0x013dcbfd50000000 0xedc7dfffc0000000 0xddb8fbfff8000000

def z1071 : W := mkw 0x096c0fea96c06a80 0x812d81fd52d80d50 0xf7fc0ff03fc07fc7 0xbeff81fe07f80ff8

def z1072 : W := mkw 0x0135b0003b750007 0x0026b600076ea000 0xe3fc30003fff8007 0x3c7f860007fff000

def z1073 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x73f80f803f807fc5 0xae7f01f007f00ff8

def z1074 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x53fc0f803fc07fc4 0xaa7f81f007f80ff8

def z1075 : W := mkw 0x09ff7fea84806a80 0x813feffd50900d50 0xfffffffffc007fc3 0xffffffffff800ff8

def z1076 : W := mkw 0x09ff7fea80802200 0x813feffd50100440 0xedffffffc3800304 0xfdbffffff8700060

def z1077 : W := mkw 0x40008015602a957c 0x48001002ac0552af 0x10000000207fffff 0x02000000040fffff

def z1078 : W := mkw 0x0135a00033640004 0x0026b400066c8000 0xe3fff0003fff8007 0x7c7ffe0007fff000

def z1079 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3ee7c3c3e7c3f 0xfff87dcf8787cf87

def z1080 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x4c3b8c7023a07038 0x4987718e04740e07

def z1081 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x0c03f07fc03f8000 0x41807e0ff807f000

def z1082 : W := mkw 0x00480f0004806a00 0x800901e000900d40 0xf3fc0f803fc07fc7 0xbe7f81f007f80ff8

def z1083 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x8804738fc07f8ffe 0x71008e71f80ff1ff

def z1084 : W := mkw 0x09b7706a93450001 0x0136ee0d5268a000 0x0c3ff07fc3c78004 0x6187fe0ff878f000

def z1085 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x63fba0003fff8007 0x6c7f740007fff000

def z1086 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffff8fffffc07fc7 0xbffff1fffff80ff8

def z1087 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffc0000c03 0xffbffffff8000180

def z1088 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedff8fffc0000000 0xbdbff1fff8000000

def z1089 : W := mkw 0x016c0fc816c06a80 0x802d81f902d80d50 0xfffc0ffc3fc07fc7 0xbfff81ff87f80ff8

def z1090 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xc3fc0f803fc07fc6 0x387f81f007f80ff8

def z1091 : W := mkw 0x01640a0016404800 0x002c814002c80900 0xf3fc0f803fc07fc7 0xbe7f81f007f80ff8

def z1092 : W := mkw 0x01f77a4800000000 0x003eef4900000000 0xedffffffc0000000 0xfdbffffff8000000

def z1093 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xefc3cc7c3c38703b 0x5df8798f87870e07

def z1094 : W := mkw 0x40000005400a8558 0x08000000a80150ab 0x9804738fc07f8ffa 0xd3008e71f80ff1ff

def z1095 : W := mkw 0x09ff7fea92c02200 0x813feffd52580440 0xffffffffffc07307 0xfffffffffff80e60

def z1096 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7de7c3c79fc3b 0xdff8fbcf878f3f87

def z1097 : W := mkw 0xc400801561aeb77c 0xd8801002ac35d6ef 0x1000000023a67ffd 0x020000000474cfff

def z1098 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc3cffc3c387ffb 0xdff879ff87870fff

def z1099 : W := mkw 0x017d2fa200000000 0x002fa5f440000000 0xedffffffc0000000 0xfdbffffff8000000

def z1100 : W := mkw 0x4293f05d693f957f 0x68527e0bad27f2af 0x0c03f07fc03f8038 0x41807e0ff807f007

def z1101 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0260005 0xfdbffffff804c000

def z1102 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0x7c3bad7323e7f3fd 0xef8775ae647cfe7f

def z1103 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc3ce7c3c79fcfb 0xdff879cf878f3f9f

def z1104 : W := mkw 0x0000801020201024 0x4000100204040204 0x7c3b8c7023a0703d 0xef87718e04740e07

def z1105 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffe0007001 0xffbffffffc000e00

def z1106 : W := mkw 0x09ff7fea92400080 0x013feffd52480010 0xedffffffc04000c0 0xfdbffffff8080018

def z1107 : W := mkw 0x09ff7fea96404880 0x013feffd52c80910 0xefffffffffc00cc7 0xfdfffffffff80198

def z1108 : W := mkw 0x08480fea80000000 0x010901fd50000000 0x6c038fffc0000000 0xcd8071fff8000000

def z1109 : W := mkw 0x03e64a4c1e584c12 0x207cc94983cb0982 0x83c4420c1c580c02 0x10788841838b0180

def z1110 : W := mkw 0x8419a5b321a633ac 0xd08334b66434c675 0x7c3badf323a673fd 0xef8775be6474ce7f

def z1111 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0598002 0xfdbffffff80b3000

def z1112 : W := mkw 0x08d37aea80000000 0x011a6f5d50000000 0x0c03f2ffc0000000 0x41807e5ff8000000

def z1113 : W := mkw 0x089b756a80000000 0x01136ead50000000 0x4c3bfc7fc0000000 0x49877f8ff8000000

def z1114 : W := mkw 0x09bf756a80000000 0x0137eead50000000 0xedfffd7fc0000000 0xfdbfffaff8000000

def z1115 : W := mkw 0x09f77aea80000000 0x013eef5d50000000 0xadc7f3ffc0000000 0xf5b8fe7ff8000000

def z1116 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xfbfc0f8fffc07fc7 0xbf7f81f1fff80ff8

def z1117 : W := mkw 0x012c050012c02200 0x802580a002580440 0xf3fc0f803fc07fc7 0xbe7f81f007f80ff8

def z1118 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xc3ffd0003fff8007 0x187ffa0007fff000

def z1119 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc5f8cffc07fc7 0xbe7f8bf19ff80ff8

def z1120 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0xfc3bed7323be733f 0xff877dae6477ce67

def z1121 : W := mkw 0x012c058016c06a80 0x802580b002d80d50 0xf3fc01803fc07fc7 0x3e7f803007f80ff8

def z1122 : W := mkw 0x00c2ca5828301026 0x4018594b05060204 0xffc3ce7c3c38703b 0xdff879cf87870e07

def z1123 : W := mkw 0x09ff7fea96404880 0x013feffd52c80910 0xffffffffdc400fc7 0xfffffffffb8801f8

def z1124 : W := mkw 0x00c24a4800000000 0x0018494900000000 0xedc3cfffc0000000 0xddb879fff8000000

def z1125 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0xffc3cc703c38703b 0xdff8798e07870e07

def z1126 : W := mkw 0xc419a53361a6b36c 0xd88334a66c34d66d 0xfc3ffdf3e3fff3ff 0xff87ffbe7c7ffe7f

def z1127 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x83fff0001fff8006 0x707ffe0003fff000

def z1128 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x6c3bad7323a67038 0xed8775ae6474ce07

def z1129 : W := mkw 0x09ff7fea93450001 0x013feffd5268a000 0xedffffffc3ff8007 0xfdbffffff87ff000

def z1130 : W := mkw 0x09ff7fea88100002 0x013feffd51020000 0xefffffffdc180002 0xfdfffffffb830000

def z1131 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xc5ffffffc0000000 0x38bffffff8000000

def z1132 : W := mkw 0x09ff7fea93450001 0x013feffd5268a000 0xefffffffffc78007 0xfdfffffffff8f000

def z1133 : W := mkw 0x08592fea80000000 0x010b25fd50000000 0x0c03afffc0000000 0xc18075fff8000000

def z1134 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x5fc38e7c3c387c3b 0x8bf871cf87870f87

def z1135 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xc3fff0003fdf8006 0x387ffe0007fbf000

def z1136 : W := mkw 0xc40080157bffb77f 0xd8801002af7ff6ef 0x120000003fffffff 0x0240000007ffffff

def z1137 : W := mkw 0x8419253301863328 0xd08324a66030c665 0x7c3bad730386733c 0xef8775ae6070ce67

def z1138 : W := mkw 0x8411a01121a6332c 0xd08234022434c665 0x7c3bac7023a6733d 0xef87758e0474ce67

def z1139 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc0f803fffffc7 0xbe7f81f007fffff8

def z1140 : W := mkw 0xc493f037693f957f 0x58927e06ed27f2af 0x0c03f07fc03f8038 0x41807e0ff807f007

def z1141 : W := mkw 0xc4480fb7448afff8 0xd88901f6e8915fff 0x1c000fffc0007ff8 0x838001fff8000fff

def z1142 : W := mkw 0x00db6f6a00000000 0x001b6ded40000000 0xedffffffc0000000 0xfdbffffff8000000

def z1143 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0xac07f07fc07f8007 0x7580fe0ff80ff000

def z1144 : W := mkw 0x09b7706a92400000 0x0136ee0d52480000 0xeffff07fffc00007 0x7dfffe0ffff80000

def z1145 : W := mkw 0x09ff7fea9a510003 0x013feffd534a2000 0xefffffffdc7f8007 0xfdfffffffb8ff000

def z1146 : W := mkw 0x0893706a81050001 0x01126e0d5020a000 0x0c03f07fc0078000 0x41807e0ff800f000

def z1147 : W := mkw 0x00480f8004806a80 0x800901f000900d50 0xb0047f80007fffc7 0xf6008ff0000ffff8

def z1148 : W := mkw 0x09ff7fea97c56a81 0x813feffd52f8ad50 0xffffffffffc7ffc7 0xfffffffffff8fff8

def z1149 : W := mkw 0x853d252313c62308 0x90a7a4a46278c461 0x003c210303c60304 0x200784206078c060

def z1150 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43fff0003fff8004 0x687ffe0007fff000

def z1151 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xf3fff1003fff8307 0xfe7ffe2007fff060

def z1152 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3fc2f803fe67fc7 0xfe7f85f007fccff8

def z1153 : W := mkw 0x09ff7fea84806a80 0x813feffd50900d50 0xfdffffffc0407fc7 0xffbffffff8080ff8

def z1154 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff183ffff8007 0x7c7ffe307ffff000

def z1155 : W := mkw 0x0082404800000000 0x0010480900000000 0x0c03f07fc0000000 0x41807e0ff8000000

def z1156 : W := mkw 0x40480f85448aefd8 0x880901f0a8915dfb 0x10000f8000007ff8 0x820001f000000fff

def z1157 : W := mkw 0x8411a0332126112c 0x508234066424c225 0x7c3bac7323a6703d 0xef87758e6474ce07

def z1158 : W := mkw 0x01ee4fc800000000 0x003dc9f900000000 0xedffffffc0000000 0xfdbffffff8000000

def z1159 : W := mkw 0x8d3d35a393c72309 0x91a7a6b47278e461 0x003c3183c3c78304 0x200786307878f060

def z1160 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x7c3bad7323807338 0xef8775ae64700e67

def z1161 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xd7c3ce7c3c387c3b 0x1af879cf87870f87

def z1162 : W := mkw 0x0000801020201024 0x4000100204040204 0xffc38c703c20703b 0xdff8718e07840e07

def z1163 : W := mkw 0x0019a53220a03224 0xc00334a644140644 0x7c3bad7323a0733d 0xef8775ae64740e67

def z1164 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x43ffb0003fff8007 0x287ff60007fff000

def z1165 : W := mkw 0x09ff7fea96c06a80 0x813feffd52d80d50 0xffffffffff807c03 0xfffffffffff00f80

def z1166 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7defcfc387c3b 0xdff8fbdf9f870f87

def z1167 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0xffc3ce7c3c207039 0xdff879cf87840e07

def z1168 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xf3f80e003fc07fc7 0x9e7f01c007f80ff8

def z1169 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff3803fff8007 0xfc7ffe7007fff000

def z1170 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x4dfb8c7fc0000000 0x09bf718ff8000000

def z1171 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xf3fffc003ffff007 0xfe7fff8007fffe00

def z1172 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0x53f80f803fc07fc7 0x8a7f01f007f80ff8

def z1173 : W := mkw 0x8408853320a2332c 0xd08110a664144665 0x7c3b8d7323a0733d 0xef8771ae64740e67

def z1174 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc3cefcfc387cfb 0xdff879df9f870f9f

def z1175 : W := mkw 0x09ee4fea80000000 0x013dc9fd50000000 0xedffcfffc0000000 0xfdbff9fff8000000

def z1176 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xefc3ce7c3c387038 0xddf879cf87870e07

def z1177 : W := mkw 0x02c2ca582c305826 0x6058594b05860b04 0x57c38c703c207039 0x0af8718e07840e07

def z1178 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffe3800005 0xfdbffffffc700000

def z1179 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0478004 0xfdbffffff808f000

def z1180 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x543bad7323a6733d 0x2a8775ae6474ce67

def z1181 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff28cffff8007 0x7c7ffe519ffff000

def z1182 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc38e7c3c007c3b 0x9ff871cf87800f87

def z1183 : W := mkw 0x420080156c3add7e 0x68401002ad875baf 0x120000003c387ffb 0x0240000007870fff

def z1184 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x0c3fffffc0000000 0xe187fffff8000000

def z1185 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x4c3b8c7323807038 0x0987718e64700e07

def z1186 : W := mkw 0x8419a53321a6332c 0xd08334a66434c665 0x6c3bac7323a6703d 0x6d87758e6474ce07

def z1187 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xcdfffeffc0000000 0x59bfffdff8000000

def z1188 : W := mkw 0x420080156c3add7e 0x68401002ad875baf 0x120000003c3ffc3b 0x024000000787ff87

def z1189 : W := mkw 0x016c0f8016c06a80 0x802d81f002d80d50 0xfbfc7f8fffffffc7 0xff7f8ff1fffffff8

def z1190 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x7c3bad7323a07039 0xef8775ae64740e07

def z1191 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0xe3fff1803fff83c7 0x7c7ffe3007fff078

def z1192 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xfdffffffc0000305 0xffbffffff8000060

def z1193 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0xffc7fffffc7ffc3f 0xfff8ffffff8fff87

def z1194 : W := mkw 0x09ff7fea84806a80 0x813feffd50900d50 0xfdffffffe3807fc5 0xffbffffffc700ff8

def z1195 : W := mkw 0xc6480f7f448aff78 0xf8c901efe8915fef 0x1c000fffc0007ff8 0x838001fff8000fff

def z1196 : W := mkw 0xc56c8f9577eefffc 0xd8ad91f2aefddfff 0xf3fc0f803fffffff 0xbe7f81f007ffffff

def z1197 : W := mkw 0x089b75ea80000000 0x01136ebd50000000 0x0c03f1ffc0000000 0x41807e3ff8000000

def z1198 : W := mkw 0x017d2fa216c06a80 0x802fa5f442d80d50 0xffffffffffc07fc7 0xfffffffffff80ff8

def z1199 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0x4dfbffffc0000000 0xc9bf7ffff8000000

def z1200 : W := mkw 0x09ff7fea80000000 0x013feffd50000000 0xedffffffc0400cc2 0xfdbffffff8080198

def z1201 : W := mkw 0x01b7f0003b750007 0x0036fe00076ea000 0x83fc70003fff8007 0x307f8e0007fff000

def z1202 : W := mkw 0x09f77aea80000000 0x013eef5d50000000 0x0dc3f07fc0000000 0x41b87e0ff8000000

def z1203 : W := mkw 0x08d37a6a84004800 0x011a6f4d50800900 0xffc3fe7ffc007c03 0xdff87fcfff800f80

def z1204 : W := mkw 0x09ff7fea96404880 0x013feffd52c80910 0xefffffffdc000000 0xfdfffffffb800000

def z1205 : W := mkw 0x08ca4fea80000000 0x011949fd50000000 0x4dc38fffc0000000 0x89b871fff8000000

def z1206 : W := mkw 0x0124000016c06a80 0x8024800002d80d50 0x53f800003fc07fc7 0x0a7f000007f80ff8

def z1207 : W := mkw 0x853d25a313c62388 0x90a7a4b46278c471 0x0038210303860304 0x200704206070c060

def z1208 : W := mkw 0x42c2ca5c6c38dc76 0x6858594b8d871b8e 0xffc7fefcfc7ffcff 0xfff8ffdf9f8fff9f

def z1209 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x7c3bac7023a6703d 0xef87758e0474ce07

def z1210 : W := mkw 0x8419a53221a43224 0xd08334a644348644 0x5c3b8c7023807038 0x8b87718e04700e07

def z1211 : W := mkw 0x0893706a80000000 0x01126e0d50000000 0x6c3bf07fc0000000 0x6d877e0ff8000000

def z1212 : W := mkw 0xc53d25a353c6a3c8 0x98a7a4b46a78d479 0x003c3183c3c783c4 0x200786307878f078

def z1213 : W := mkw 0x02c2ca5c2c385c36 0x6058594b85870b86 0x4fc38c7c3c007038 0x09f8718f87800e07

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z5,z8,z6]),(0,[z9,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z10,z2,z3,z5,z6]),(1,[z1,z11,z2,z4,z5,z6]),(0,[z1,z7,z2,z3,z12,z5,z6]),(0,[z13,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z14])],[(0,[z15,z16,z1,z7,z2,z5,z6]),(0,[z1,z7,z2,z3,z5,z17,z6])],[(0,[z0,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z18,z19,z5,z6]),(1,[z20,z1,z2,z21,z5,z6]),(0,[z1,z22,z2,z3,z23,z5,z6]),(0,[z1,z7,z2,z24,z3,z5,z25])],[(0,[z1,z7,z26,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z27,z6]),(0,[z1,z7,z2,z3,z5,z6,z28]),(0,[z1,z7,z2,z3,z5,z29,z6]),(0,[z1,z7,z2,z3,z5,z6,z30])],[(0,[z1,z7,z31,z2,z19,z5,z6]),(0,[z1,z7,z2,z32,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z33]),(0,[z1,z7,z2,z3,z5,z34,z6]),(0,[z1,z7,z2,z35,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z36,z6]),(0,[z1,z7,z2,z3,z5,z6,z37]),(0,[z1,z7,z2,z3,z5,z6,z38]),(0,[z1,z7,z2,z39,z3,z5,z6])],[(0,[z40,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z41,z5,z6,z42]),(0,[z1,z43,z2,z44,z3,z5,z6]),(0,[z45,z1,z7,z2,z3,z5,z6])],[(0,[z46,z7,z2,z3,z5,z47,z6]),(0,[z1,z7,z2,z48,z3,z5,z6]),(0,[z49,z50,z1,z7,z3,z5,z6]),(0,[z51,z1,z7,z2,z3,z5,z6]),(0,[z1,z52,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z21,z5,z25,z6]),(1,[z1,z53,z2,z3,z5,z6])]],
   [[(0,[z54,z1,z7,z2,z3,z5,z6]),(0,[z55,z1,z7,z2,z3,z5,z6]),(0,[z56,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z57,z5,z6]),(0,[z1,z7,z2,z58,z44,z3,z5]),(0,[z1,z59,z7,z2,z3,z5,z6]),(0,[z60,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z61,z2,z3,z5,z6])],[(0,[z46,z0,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z62]),(0,[z1,z7,z2,z3,z5,z6,z63]),(0,[z1,z7,z3,z5,z64,z65,z6]),(0,[z15,z1,z7,z2,z3,z66,z6])],[(0,[z67,z1,z7,z2,z3,z5,z6]),(0,[z0,z1,z31,z2,z3,z5,z6]),(0,[z68,z1,z7,z2,z69,z5,z6]),(0,[z70,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z71,z6])],[(0,[z72,z1,z7,z2,z3,z5,z6]),(0,[z73,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z19,z74,z5,z6]),(0,[z1,z7,z2,z75,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z76,z6]),(0,[z77,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z78,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z79]),(0,[z1,z7,z2,z3,z5,z80,z6])],[(0,[z7,z31,z2,z3,z5,z47,z6]),(0,[z81,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z82,z2,z3,z5,z6]),(0,[z1,z83,z7,z2,z3,z5,z6])],[(0,[z84,z7,z2,z3,z5,z47,z6]),(0,[z1,z7,z2,z3,z5,z85,z6])],[(0,[z1,z7,z86,z2,z3,z5,z6]),(0,[z1,z7,z87,z2,z19,z5,z6]),(0,[z88,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z4,z5,z25,z6]),(0,[z89,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z90,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z91,z5,z6]),(1,[z13,z1,z7,z2,z5,z92])]],
   [[(1,[z1,z7,z2,z93,z5,z6]),(0,[z94,z1,z7,z2,z19,z5,z6])],[(0,[z95,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z96]),(1,[z1,z7,z2,z97,z5,z6]),(0,[z1,z7,z2,z98,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z99])],[(0,[z1,z7,z2,z2,z3,z5,z6]),(0,[z1,z100,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z101,z19,z5,z6]),(0,[z1,z7,z2,z41,z5,z102,z6]),(0,[z1,z7,z103,z2,z3,z5,z6]),(0,[z1,z7,z44,z3,z5,z64,z6]),(0,[z1,z7,z2,z3,z5,z6,z104])],[(0,[z105,z1,z7,z106,z3,z5,z6]),(0,[z107,z1,z22,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z108]),(0,[z49,z1,z7,z3,z5,z6,z109]),(0,[z1,z110,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z111,z5,z6])],[(0,[z112,z1,z7,z2,z3,z5,z6])],[(0,[z113,z1,z7,z2,z3,z5,z6]),(0,[z114,z50,z1,z2,z3,z5,z6]),(0,[z50,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z90,z3,z5,z65,z6]),(0,[z1,z115,z7,z2,z3,z5,z6]),(0,[z15,z1,z7,z2,z116,z5,z6])],[(0,[z84,z1,z7,z2,z19,z5,z6]),(0,[z1,z22,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z117,z3,z5,z6]),(0,[z1,z2,z3,z23,z5,z29,z6]),(0,[z1,z7,z2,z3,z5,z64,z6])]],
   [[(0,[z1,z7,z2,z3,z5,z118,z6]),(0,[z1,z7,z119,z90,z3,z5,z6]),(0,[z1,z7,z2,z41,z5,z120,z6]),(0,[z1,z7,z2,z121,z3,z5,z6])],[(0,[z1,z7,z2,z41,z5,z6,z122]),(0,[z1,z7,z2,z21,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z123,z6]),(0,[z1,z7,z2,z3,z5,z65,z6]),(0,[z1,z7,z2,z3,z5,z124,z6]),(0,[z1,z7,z2,z3,z5,z25,z122]),(0,[z1,z7,z2,z3,z125,z5,z6])],[(0,[z126,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z127,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z128]),(1,[z1,z7,z90,z3,z129,z6])],[(0,[z130,z1,z7,z119,z3,z5,z6]),(0,[z1,z7,z2,z19,z5,z131,z6]),(0,[z20,z1,z7,z2,z4,z5,z6]),(0,[z107,z132,z7,z2,z3,z5,z6]),(0,[z133,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z134,z90,z3,z5,z6]),(0,[z49,z1,z7,z90,z3,z5,z6]),(0,[z1,z135,z7,z2,z3,z5,z6])],[(0,[z1,z7,z136,z2,z3,z5,z6]),(1,[z7,z2,z41,z5,z47,z6]),(0,[z137,z1,z7,z87,z2,z3,z5]),(0,[z1,z7,z2,z21,z116,z5,z6]),(0,[z138,z1,z7,z2,z3,z5,z6])],[(0,[z7,z119,z2,z101,z3,z5,z6]),(0,[z49,z137,z1,z7,z2,z3,z5]),(0,[z139,z1,z7,z2,z3,z5,z6]),(0,[z50,z1,z7,z3,z5,z65,z6]),(0,[z1,z7,z43,z90,z3,z5,z6])],[(0,[z1,z7,z2,z140,z3,z5,z6]),(0,[z1,z7,z2,z19,z5,z47,z6]),(0,[z1,z7,z2,z19,z5,z141,z6]),(0,[z1,z7,z2,z3,z142,z5,z6]),(0,[z1,z7,z2,z143,z3,z5,z6]),(0,[z144,z1,z7,z2,z3,z129,z6]),(0,[z1,z145,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z92])],[(0,[z146,z1,z7,z2,z3,z5,z6]),(1,[z147,z1,z2,z3,z5,z6]),(0,[z68,z1,z7,z2,z148,z5,z6]),(0,[z1,z7,z90,z2,z3,z64,z6]),(0,[z15,z1,z7,z2,z5,z120,z6]),(0,[z1,z7,z149,z3,z125,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z150])]],
   [[(0,[z20,z46,z1,z2,z3,z5,z6]),(0,[z114,z1,z2,z44,z3,z5,z6]),(1,[z1,z7,z151,z3,z5,z6]),(0,[z1,z7,z87,z2,z3,z5,z152])],[(0,[z153,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z154,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z155,z6]),(0,[z156,z1,z7,z2,z19,z5,z6]),(1,[z1,z2,z19,z157,z5,z6]),(0,[z158,z1,z7,z2,z3,z5,z6]),(0,[z1,z159,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z160,z5,z6])],[(0,[z161,z1,z7,z2,z3,z5,z6]),(0,[z20,z1,z7,z2,z21,z5,z6]),(0,[z162,z1,z7,z2,z3,z5,z6])],[(1,[z1,z7,z2,z41,z5,z6]),(0,[z137,z7,z2,z3,z5,z131,z6]),(0,[z144,z1,z7,z90,z3,z5,z6])],[(0,[z163,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z164,z2,z3,z5,z6]),(0,[z1,z59,z2,z44,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z165,z6]),(0,[z1,z7,z2,z21,z5,z120,z6]),(1,[z166,z7,z2,z3,z5,z6]),(0,[z1,z59,z7,z2,z3,z5,z102]),(0,[z1,z59,z2,z3,z5,z102,z6]),(0,[z1,z7,z2,z3,z167,z5,z6]),(0,[z168,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z19,z24,z5,z6]),(0,[z1,z7,z2,z3,z5,z152,z30]),(0,[z1,z7,z2,z3,z169,z5,z6]),(0,[z170,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z171,z3,z5,z6])],[(1,[z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z172,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z173]),(0,[z1,z7,z2,z3,z174,z5,z6]),(0,[z175,z1,z59,z2,z3,z5,z6]),(0,[z176,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z177,z3,z5,z6])]],
   [[(0,[z46,z1,z7,z2,z178,z5,z6]),(0,[z1,z7,z2,z3,z179,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z180]),(0,[z181,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z182]),(0,[z183,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z184,z6]),(0,[z1,z7,z2,z3,z5,z6,z185])],[(0,[z107,z0,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z186]),(0,[z147,z1,z2,z19,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z187,z6]),(0,[z1,z7,z2,z19,z66,z5,z6]),(0,[z188,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z189]),(0,[z190,z1,z7,z2,z3,z5,z6])],[(0,[z105,z1,z7,z2,z191,z5,z6]),(0,[z1,z11,z7,z2,z21,z5,z6]),(1,[z15,z1,z7,z2,z120,z6]),(0,[z1,z7,z2,z192,z3,z5,z6])],[(0,[z193,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z19,z5,z6,z109]),(0,[z1,z7,z194,z2,z3,z5,z6]),(0,[z195,z1,z7,z2,z3,z5,z6]),(0,[z16,z1,z7,z2,z196,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z197]),(0,[z1,z7,z2,z3,z5,z6,z198])],[(0,[z1,z7,z199,z2,z3,z5,z6]),(0,[z20,z1,z7,z2,z41,z5,z6]),(0,[z107,z1,z7,z2,z200,z5,z6]),(0,[z1,z7,z2,z3,z5,z201,z6]),(0,[z15,z135,z7,z2,z3,z5,z6]),(1,[z1,z7,z202,z3,z5,z6])],[(0,[z175,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z203]),(0,[z204,z7,z2,z21,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z205,z6]),(0,[z206,z1,z7,z2,z3,z5,z6]),(0,[z15,z1,z7,z134,z2,z5,z6]),(0,[z1,z7,z2,z3,z5,z207,z6])]],
   [[(0,[z1,z7,z208,z2,z3,z5,z6]),(0,[z1,z7,z2,z209,z3,z5,z6]),(0,[z1,z7,z2,z19,z19,z5,z6]),(0,[z49,z156,z1,z7,z2,z3,z5]),(1,[z1,z210,z2,z3,z5,z6])],[(0,[z1,z7,z211,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z212,z6]),(0,[z1,z213,z7,z2,z3,z5,z6]),(0,[z1,z7,z214,z2,z3,z5,z6])],[(1,[z126,z7,z119,z3,z5,z6]),(0,[z20,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z102,z122])],[(0,[z215,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z216,z41,z5,z6]),(0,[z1,z7,z2,z217,z3,z5,z6]),(0,[z1,z7,z2,z3,z129,z5,z218]),(1,[z1,z7,z2,z3,z5,z219]),(0,[z1,z7,z2,z3,z5,z6,z220])],[(0,[z221,z1,z7,z2,z3,z5,z6]),(0,[z222,z1,z7,z2,z41,z5,z6]),(0,[z107,z1,z7,z2,z19,z5,z6]),(0,[z223,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z224,z3,z5,z6]),(0,[z1,z7,z2,z3,z225,z5,z6]),(0,[z1,z7,z2,z3,z226,z5,z6])],[(0,[z130,z1,z7,z101,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z227,z6]),(0,[z1,z7,z2,z41,z5,z131,z6]),(0,[z1,z7,z2,z3,z5,z6,z228]),(1,[z114,z1,z44,z3,z5,z6]),(0,[z1,z7,z2,z3,z229,z5,z6]),(0,[z107,z1,z7,z2,z3,z29,z6]),(0,[z230,z1,z7,z3,z5,z6,z30]),(0,[z1,z7,z2,z3,z125,z152,z6])],[(0,[z68,z1,z7,z2,z19,z5,z6]),(0,[z231,z1,z7,z2,z3,z5,z6])],[(0,[z68,z1,z7,z2,z41,z5,z6]),(0,[z107,z166,z7,z2,z3,z5,z6]),(0,[z175,z1,z2,z3,z5,z6,z30]),(0,[z1,z7,z2,z3,z5,z232,z6])]],
   [[(0,[z68,z7,z31,z2,z3,z5,z6]),(0,[z233,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z41,z5,z47,z6]),(0,[z234,z1,z7,z2,z3,z5,z6]),(0,[z235,z1,z2,z3,z5,z47,z6]),(0,[z1,z7,z2,z236,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z237]),(0,[z13,z1,z7,z2,z66,z5,z6]),(0,[z222,z1,z7,z2,z3,z5,z6])],[(0,[z0,z1,z7,z2,z238,z5,z6]),(1,[z1,z7,z2,z209,z5,z6]),(0,[z239,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z240,z6]),(0,[z1,z7,z241,z2,z3,z5,z6]),(0,[z1,z11,z2,z3,z4,z5,z6]),(0,[z1,z7,z3,z129,z5,z64,z6])],[(0,[z1,z7,z2,z3,z5,z242,z6]),(1,[z1,z7,z2,z69,z5,z6]),(0,[z1,z7,z2,z243,z3,z5,z6]),(1,[z204,z7,z2,z3,z5,z6])],[(0,[z1,z7,z244,z2,z19,z5,z6]),(1,[z1,z245,z2,z3,z5,z6]),(0,[z1,z7,z2,z246,z3,z5,z6]),(0,[z1,z11,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z247,z6]),(1,[z1,z7,z2,z248,z5,z6]),(0,[z49,z1,z7,z2,z3,z5,z122]),(0,[z1,z7,z87,z2,z3,z5,z65])],[(0,[z16,z1,z7,z134,z3,z5,z6]),(0,[z1,z7,z2,z3,z249,z5,z6]),(0,[z49,z1,z53,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z250]),(0,[z15,z1,z7,z251,z3,z5,z6]),(0,[z252,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z253,z6]),(0,[z1,z7,z2,z3,z5,z92,z122])],[(0,[z1,z7,z2,z3,z254,z5,z6]),(0,[z1,z7,z2,z255,z3,z5,z6]),(0,[z1,z7,z256,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z257,z6])],[(0,[z13,z1,z7,z2,z19,z5,z6]),(0,[z137,z1,z7,z2,z3,z5,z131]),(0,[z107,z1,z7,z2,z3,z5,z38]),(0,[z1,z7,z2,z3,z5,z258,z6]),(0,[z1,z7,z2,z259,z3,z5,z6])],[(0,[z260,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z261,z3,z5,z6]),(0,[z126,z1,z7,z2,z262,z5,z6]),(0,[z13,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z263]),(0,[z1,z7,z2,z58,z3,z5,z6]),(0,[z1,z2,z21,z3,z4,z5,z6]),(0,[z264,z1,z7,z2,z3,z5,z6]),(0,[z1,z265,z7,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z7,z2,z19,z5,z6]),(0,[z49,z130,z1,z7,z3,z5,z6]),(0,[z1,z7,z266,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z267,z5,z6]),(0,[z1,z7,z2,z5,z268,z64,z6]),(0,[z269,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z270,z5,z6]),(0,[z1,z7,z2,z19,z129,z5,z6]),(0,[z1,z7,z2,z3,z5,z271,z6]),(0,[z7,z2,z3,z5,z131,z6,z228]),(0,[z1,z7,z2,z272,z3,z5,z6]),(0,[z1,z7,z3,z5,z65,z6,z109])],[(0,[z0,z7,z31,z2,z3,z5,z6]),(0,[z126,z1,z7,z119,z3,z5,z6]),(0,[z1,z7,z2,z32,z19,z5,z6]),(0,[z273,z1,z7,z2,z3,z5,z6]),(0,[z274,z1,z7,z2,z3,z5,z6])],[(0,[z1,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z275,z3,z5,z6]),(0,[z276,z1,z7,z2,z3,z5,z6]),(0,[z277,z7,z2,z3,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z152,z6]),(0,[z137,z1,z7,z2,z255,z5,z6]),(0,[z50,z1,z7,z2,z97,z5,z6]),(0,[z1,z7,z2,z3,z278,z5,z6]),(0,[z1,z7,z2,z279,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z280,z6]),(0,[z1,z7,z2,z3,z5,z6,z281])],[(0,[z1,z7,z266,z2,z3,z5,z6]),(0,[z114,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z41,z66,z5,z6]),(0,[z1,z7,z2,z282,z3,z5,z6]),(0,[z1,z7,z2,z283,z3,z5,z6]),(0,[z15,z1,z7,z2,z5,z25,z6]),(0,[z1,z7,z2,z116,z3,z120,z6])],[(0,[z1,z31,z2,z3,z5,z29,z6]),(0,[z84,z284,z7,z2,z3,z5,z6]),(0,[z84,z7,z2,z19,z3,z5,z6]),(0,[z285,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z286,z6])],[(0,[z287,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z288,z41,z5,z6]),(0,[z55,z1,z7,z2,z19,z5,z6]),(0,[z156,z1,z7,z2,z289,z5,z6]),(0,[z290,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z291,z3,z5,z6]),(0,[z292,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z293,z6])],[(0,[z130,z7,z2,z101,z3,z5,z6]),(0,[z1,z7,z2,z41,z5,z6,z109]),(0,[z137,z1,z7,z2,z294,z5,z6]),(0,[z1,z7,z295,z2,z3,z5,z6]),(0,[z1,z7,z296,z2,z3,z5,z6]),(0,[z1,z7,z2,z297,z3,z5,z6]),(1,[z175,z1,z2,z3,z5,z30]),(0,[z1,z7,z2,z3,z5,z6,z298]),(0,[z1,z7,z2,z299,z3,z5,z6])]],
   [[(0,[z1,z59,z7,z2,z41,z5,z6]),(0,[z114,z1,z7,z2,z3,z5,z6]),(0,[z300,z1,z7,z2,z3,z5,z6]),(1,[z1,z301,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z302])],[(0,[z1,z7,z303,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z23,z5,z6]),(0,[z156,z1,z7,z2,z282,z5,z6]),(0,[z1,z7,z304,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z305,z5,z6]),(0,[z1,z7,z2,z3,z5,z306,z6])],[(0,[z0,z7,z2,z3,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z307,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z67,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z131,z152]),(0,[z308,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z309,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z310])],[(0,[z1,z7,z2,z41,z41,z5,z6])],[(0,[z46,z1,z7,z2,z3,z5,z6]),(1,[z132,z7,z2,z3,z5,z6]),(0,[z1,z22,z7,z2,z3,z23,z6]),(0,[z1,z7,z2,z311,z3,z5,z6]),(0,[z15,z312,z7,z2,z3,z5,z6])],[(0,[z1,z7,z90,z2,z19,z5,z6]),(1,[z1,z313,z2,z3,z5,z6]),(0,[z105,z1,z7,z2,z3,z47,z6]),(0,[z1,z7,z2,z3,z314,z5,z6])],[(0,[z1,z7,z2,z3,z5,z315,z6]),(0,[z1,z7,z2,z3,z5,z316,z6]),(0,[z130,z1,z7,z2,z179,z5,z6]),(0,[z1,z7,z90,z2,z41,z5,z6]),(1,[z1,z7,z2,z3,z5,z317]),(1,[z1,z7,z2,z148,z5,z6])],[(0,[z318,z1,z7,z2,z3,z5,z6]),(0,[z319,z1,z7,z2,z41,z5,z6]),(0,[z114,z1,z7,z3,z5,z65,z6]),(0,[z1,z7,z2,z3,z5,z6,z320]),(0,[z1,z59,z7,z2,z3,z5,z30]),(0,[z1,z7,z2,z3,z321,z5,z6]),(0,[z322,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z24,z3,z5,z92])]],
   [[(0,[z323,z1,z7,z2,z3,z5,z6]),(0,[z20,z1,z22,z2,z3,z5,z6]),(0,[z107,z1,z7,z2,z324,z5,z6])],[(0,[z1,z7,z2,z93,z3,z5,z6]),(0,[z156,z1,z7,z87,z2,z3,z5]),(0,[z16,z1,z7,z2,z4,z5,z6]),(0,[z1,z7,z90,z3,z196,z5,z6])],[(1,[z1,z7,z2,z48,z5,z6]),(0,[z1,z7,z2,z3,z5,z325,z6]),(0,[z1,z7,z2,z3,z5,z6,z326]),(0,[z1,z7,z2,z3,z5,z327,z6]),(0,[z1,z7,z2,z3,z5,z328,z6]),(0,[z1,z7,z2,z3,z5,z6,z329])],[(1,[z277,z7,z2,z41,z5,z6]),(0,[z319,z1,z7,z2,z3,z5,z6]),(1,[z1,z330,z2,z3,z5,z6]),(0,[z331,z1,z7,z2,z3,z5,z6])],[(0,[z84,z0,z7,z2,z3,z5,z6]),(0,[z46,z1,z7,z2,z332,z5,z6]),(0,[z50,z1,z7,z2,z19,z5,z6]),(1,[z333,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z3,z5,z6,z334]),(0,[z1,z7,z2,z3,z196,z5,z6]),(0,[z335,z1,z7,z2,z3,z5,z6])],[(0,[z46,z1,z31,z2,z3,z5,z6]),(0,[z50,z1,z7,z2,z41,z5,z6]),(0,[z1,z336,z7,z2,z3,z5,z6])],[(0,[z105,z1,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z127,z5,z47,z6]),(0,[z1,z7,z2,z3,z337,z5,z6]),(0,[z15,z1,z7,z2,z3,z5,z6])],[(0,[z338,z1,z7,z2,z3,z5,z6]),(0,[z107,z1,z7,z339,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z340]),(0,[z341,z1,z7,z2,z3,z5,z6]),(0,[z13,z1,z7,z2,z3,z5,z25]),(0,[z1,z7,z2,z342,z3,z5,z6])]],
   [[(0,[z284,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z21,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z152,z228]),(0,[z16,z1,z7,z2,z21,z5,z6]),(0,[z1,z7,z2,z3,z5,z120,z6])],[(0,[z1,z7,z119,z2,z3,z5,z6]),(0,[z343,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z344,z3,z5,z6]),(0,[z204,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z345,z6]),(0,[z1,z7,z2,z3,z5,z6,z122])],[(0,[z130,z126,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z346,z6])],[(0,[z1,z7,z2,z41,z129,z5,z6]),(0,[z156,z1,z7,z2,z3,z5,z228]),(0,[z1,z347,z7,z2,z3,z5,z6]),(0,[z348,z1,z7,z2,z3,z5,z6]),(0,[z222,z1,z7,z2,z3,z125,z6]),(1,[z222,z1,z7,z2,z3,z122]),(0,[z1,z7,z149,z2,z3,z5,z6])],[(0,[z284,z1,z7,z2,z3,z5,z6]),(0,[z126,z1,z7,z101,z3,z5,z6]),(0,[z1,z7,z349,z2,z3,z5,z6]),(0,[z50,z1,z2,z3,z5,z6,z30]),(0,[z1,z7,z2,z350,z3,z5,z6]),(0,[z1,z351,z7,z2,z3,z5,z6]),(0,[z49,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z352,z6]),(0,[z1,z7,z2,z41,z5,z152,z6]),(0,[z1,z7,z353,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z354,z5,z6]),(0,[z15,z1,z7,z202,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z355])],[(1,[z1,z7,z2,z238,z5,z6]),(0,[z356,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z119,z3,z5,z64,z6]),(0,[z1,z7,z2,z3,z357,z5,z6]),(0,[z358,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z268,z6])],[(0,[z1,z7,z2,z3,z359,z5,z6]),(0,[z1,z7,z2,z3,z5,z360,z6]),(1,[z1,z7,z2,z200,z5,z6]),(0,[z175,z1,z7,z87,z2,z3,z5]),(0,[z1,z7,z2,z3,z5,z6,z361]),(0,[z15,z1,z210,z2,z3,z5,z6])]],
   [[(0,[z1,z59,z7,z2,z248,z5,z6]),(1,[z144,z1,z7,z3,z64,z6]),(0,[z1,z7,z2,z3,z362,z5,z6])],[(0,[z363,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z364]),(0,[z1,z7,z2,z3,z5,z365,z6]),(0,[z1,z7,z134,z3,z5,z64,z6]),(0,[z49,z1,z7,z3,z5,z64,z6]),(0,[z13,z1,z7,z2,z3,z5,z92]),(0,[z1,z7,z2,z3,z5,z6,z366])],[(0,[z367,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z368,z5,z6]),(0,[z369,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z370,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z371,z6]),(1,[z1,z7,z2,z291,z5,z6]),(0,[z1,z7,z2,z372,z3,z5,z6])],[(0,[z1,z7,z2,z41,z23,z5,z6]),(0,[z1,z7,z43,z3,z5,z64,z6]),(0,[z1,z7,z2,z373,z3,z5,z6]),(0,[z1,z7,z2,z3,z374,z5,z6])],[(0,[z1,z7,z2,z375,z3,z5,z6]),(0,[z16,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z191,z5,z6]),(0,[z1,z7,z2,z3,z376,z5,z6]),(0,[z1,z7,z134,z2,z196,z5,z6]),(0,[z1,z7,z2,z116,z3,z66,z6])],[(1,[z1,z7,z2,z19,z5,z6])],[(0,[z20,z0,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z5,z29,z6]),(0,[z1,z7,z2,z19,z5,z6,z30]),(0,[z105,z1,z7,z377,z3,z5,z6]),(0,[z378,z1,z7,z2,z3,z5,z6]),(0,[z379,z1,z7,z2,z3,z5,z6]),(0,[z380,z1,z7,z2,z3,z5,z6])],[(0,[z381,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z2,z261,z3,z5]),(0,[z1,z7,z2,z382,z3,z5,z6]),(0,[z1,z11,z7,z2,z4,z5,z6]),(0,[z1,z7,z383,z2,z3,z5,z6])]],
   [[(0,[z1,z132,z7,z2,z3,z5,z6]),(0,[z16,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z384,z6]),(0,[z1,z7,z385,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z125,z5,z152])],[(0,[z1,z7,z2,z3,z5,z386,z6]),(0,[z1,z7,z151,z2,z3,z5,z6]),(0,[z144,z1,z7,z3,z5,z64,z6]),(0,[z49,z1,z7,z2,z3,z5,z109])],[(0,[z1,z7,z2,z3,z5,z387,z6]),(0,[z388,z1,z7,z2,z3,z5,z6]),(0,[z105,z1,z245,z2,z3,z5,z6])],[(1,[z84,z7,z2,z19,z5,z6]),(0,[z137,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z294,z5,z6])],[],[(0,[z1,z7,z2,z389,z3,z5,z6]),(0,[z1,z7,z2,z3,z390,z5,z6]),(0,[z391,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z87,z2,z3,z5,z122]),(0,[z1,z7,z2,z3,z5,z392,z6])],[(0,[z0,z1,z2,z3,z23,z5,z6]),(1,[z1,z2,z3,z5,z34,z6]),(0,[z68,z1,z7,z2,z3,z127,z6]),(0,[z1,z7,z2,z3,z393,z5,z6]),(0,[z1,z7,z2,z3,z394,z5,z6]),(0,[z1,z7,z2,z3,z152,z6,z122])],[(0,[z1,z7,z2,z41,z395,z5,z6]),(0,[z1,z7,z396,z2,z3,z5,z6]),(1,[z1,z7,z2,z3,z5,z38]),(0,[z397,z1,z7,z2,z3,z5,z6]),(0,[z1,z53,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z398,z5,z6]),(1,[z1,z7,z2,z24,z5,z25])]],
   [[(0,[z1,z7,z2,z3,z5,z6,z399]),(0,[z20,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z400,z5,z6]),(0,[z1,z7,z2,z66,z5,z25,z6])],[(0,[z1,z7,z2,z401,z3,z5,z6]),(0,[z1,z7,z202,z2,z3,z5,z6])],[(0,[z402,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z403,z5,z6]),(0,[z7,z2,z21,z404,z3,z5,z6]),(0,[z1,z7,z373,z3,z196,z5,z6]),(0,[z1,z7,z2,z3,z405,z5,z6])],[(0,[z1,z7,z2,z339,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z406]),(0,[z1,z7,z2,z407,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z408,z6]),(0,[z1,z7,z2,z19,z5,z6,z96]),(0,[z1,z7,z2,z3,z5,z6,z409]),(0,[z1,z7,z2,z3,z5,z6,z410]),(0,[z1,z7,z2,z5,z6,z281,z122])],[(0,[z1,z7,z2,z3,z5,z411,z6]),(0,[z1,z7,z2,z3,z5,z6,z412])],[(0,[z1,z7,z2,z41,z5,z413,z6]),(0,[z234,z1,z7,z2,z19,z5,z6]),(0,[z222,z1,z7,z2,z19,z5,z6]),(1,[z1,z7,z3,z5,z6,z364]),(0,[z414,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z41,z415,z5,z6])]],
   [[(0,[z239,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6])],[(0,[z1,z7,z2,z3,z5,z416,z6]),(1,[z1,z59,z2,z3,z5,z102])],[(0,[z1,z7,z7,z2,z3,z5,z6]),(0,[z284,z1,z22,z2,z3,z5,z6]),(0,[z1,z11,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z64,z6]),(0,[z1,z7,z2,z69,z3,z5,z6]),(0,[z1,z7,z417,z2,z3,z5,z6]),(0,[z418,z1,z7,z2,z3,z5,z6]),(0,[z419,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z420,z2,z3,z5,z6]),(0,[z421,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z422,z5,z6]),(0,[z423,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z424,z2,z3,z5,z6]),(0,[z425,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z19,z125,z5,z6]),(0,[z105,z1,z313,z2,z3,z5,z6]),(1,[z1,z7,z2,z3,z5,z218])],[(0,[z1,z7,z2,z19,z127,z5,z6]),(0,[z426,z1,z7,z2,z3,z5,z6]),(1,[z49,z1,z7,z3,z5,z109]),(0,[z1,z7,z2,z3,z5,z25,z6])],[(0,[z1,z7,z2,z3,z5,z427,z6]),(0,[z1,z7,z428,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z429,z6])],[(0,[z1,z7,z2,z3,z5,z430,z6]),(1,[z7,z2,z404,z3,z5,z6]),(0,[z107,z1,z2,z3,z5,z29,z6]),(0,[z1,z7,z2,z3,z431,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z432,z5,z6]),(0,[z1,z7,z2,z41,z5,z29,z6]),(0,[z1,z7,z2,z41,z5,z6,z30]),(1,[z235,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z433,z5,z6])],[(0,[z1,z7,z2,z18,z3,z5,z6]),(0,[z1,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z19,z5,z6,z92]),(0,[z105,z1,z7,z2,z48,z5,z6]),(0,[z1,z7,z2,z3,z434,z5,z6]),(1,[z1,z7,z2,z324,z5,z6]),(0,[z1,z7,z2,z3,z5,z435,z6])],[(0,[z1,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z436,z6]),(0,[z15,z1,z330,z2,z3,z5,z6]),(0,[z437,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z31,z2,z3,z5,z6]),(0,[z438,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z439,z5,z6]),(0,[z68,z7,z2,z3,z41,z5,z6])],[(0,[z1,z7,z101,z3,z5,z64,z6]),(1,[z1,z7,z2,z3,z5,z128]),(0,[z440,z1,z7,z2,z3,z5,z6]),(1,[z112,z1,z7,z2,z5,z6]),(0,[z1,z7,z2,z441,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z442]),(0,[z1,z7,z2,z3,z5,z152,z92])],[(0,[z443,z1,z7,z2,z3,z5,z6]),(0,[z444,z1,z7,z2,z3,z5,z6]),(0,[z445,z1,z7,z2,z3,z5,z6]),(0,[z446,z1,z7,z2,z3,z5,z6])],[(0,[z447,z1,z7,z2,z3,z5,z6]),(0,[z114,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z19,z373,z5,z6]),(0,[z448,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z90,z2,z3,z129,z6])],[(1,[z68,z7,z2,z41,z5,z6]),(0,[z175,z1,z7,z2,z3,z5,z102]),(1,[z230,z1,z7,z3,z5,z6]),(0,[z230,z1,z7,z2,z3,z5,z6]),(0,[z1,z59,z7,z2,z291,z5,z6]),(0,[z449,z1,z7,z2,z3,z5,z6]),(0,[z1,z450,z7,z2,z3,z5,z6]),(0,[z222,z1,z7,z2,z3,z5,z152])]],
   [[(0,[z451,z1,z7,z2,z3,z5,z6]),(0,[z114,z1,z7,z44,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z452]),(0,[z1,z7,z134,z2,z4,z5,z6]),(1,[z1,z7,z339,z3,z5,z6]),(0,[z1,z7,z2,z3,z453,z5,z6])],[(0,[z1,z7,z2,z3,z5,z6,z42]),(0,[z1,z7,z2,z157,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z454]),(0,[z1,z7,z2,z3,z455,z5,z6])],[(0,[z1,z7,z2,z456,z3,z5,z6]),(1,[z1,z7,z2,z262,z5,z6]),(0,[z1,z59,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z457,z6]),(1,[z1,z7,z2,z289,z5,z6]),(0,[z1,z7,z2,z3,z5,z458,z6])],[(0,[z459,z1,z7,z2,z3,z5,z6]),(0,[z46,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z460]),(0,[z1,z7,z461,z2,z3,z5,z6]),(0,[z462,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z6,z463]),(0,[z67,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z464,z5,z6])],[(0,[z1,z7,z2,z3,z5,z465,z6]),(0,[z1,z7,z2,z19,z5,z187,z6]),(1,[z1,z7,z2,z282,z5,z6]),(0,[z1,z7,z466,z2,z3,z5,z6]),(0,[z467,z1,z7,z2,z3,z5,z6])],[(0,[z468,z1,z7,z2,z3,z5,z6]),(0,[z469,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z470,z5,z6]),(0,[z1,z7,z2,z3,z5,z471,z6]),(0,[z1,z7,z2,z66,z5,z120,z6])],[(0,[z1,z7,z2,z3,z3,z5,z6]),(0,[z50,z1,z59,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z472,z5,z6]),(0,[z1,z7,z134,z2,z21,z5,z6]),(0,[z49,z1,z7,z87,z3,z5,z6]),(0,[z13,z1,z7,z2,z5,z6,z92])]],
   [[(0,[z284,z0,z1,z2,z3,z5,z6]),(0,[z473,z1,z7,z2,z3,z5,z6]),(0,[z166,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z474])],[(0,[z1,z475,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z44,z41,z5,z6]),(0,[z50,z1,z7,z43,z3,z5,z6]),(0,[z49,z175,z1,z7,z2,z3,z5])],[(0,[z1,z2,z44,z3,z5,z6,z30]),(0,[z1,z7,z90,z44,z3,z5,z6]),(0,[z476,z1,z7,z2,z3,z5,z6])],[(0,[z477,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z41,z5,z64,z6]),(0,[z15,z1,z7,z2,z19,z5,z6]),(0,[z1,z22,z2,z3,z4,z5,z6]),(0,[z1,z7,z134,z2,z66,z5,z6]),(0,[z478,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z2,z3,z5,z189])],[(0,[z105,z1,z7,z2,z41,z5,z6]),(0,[z15,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z479]),(0,[z1,z7,z480,z2,z3,z5,z6]),(0,[z1,z7,z2,z44,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z481,z6])],[(0,[z1,z7,z2,z3,z5,z482,z6]),(0,[z84,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z41,z125,z5,z6]),(0,[z1,z22,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z102,z6]),(0,[z1,z7,z2,z3,z483,z5,z6]),(0,[z1,z7,z2,z484,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z485,z6])],[(0,[z1,z7,z2,z3,z332,z5,z6]),(0,[z49,z126,z1,z7,z3,z5,z6]),(0,[z1,z7,z2,z41,z127,z5,z6]),(0,[z1,z7,z2,z344,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z131,z122]),(0,[z486,z1,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z119,z2,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z6,z228]),(0,[z1,z7,z2,z3,z487,z5,z6])],[(0,[z126,z1,z7,z2,z3,z5,z6]),(0,[z488,z1,z7,z2,z3,z5,z6]),(0,[z50,z1,z7,z44,z3,z5,z6]),(0,[z1,z7,z2,z24,z5,z25,z6]),(1,[z1,z7,z2,z3,z125,z152])],[(0,[z284,z1,z7,z2,z19,z5,z6]),(0,[z49,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z21,z19,z5,z6]),(0,[z489,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z490])],[(0,[z49,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z134,z2,z41,z5,z6]),(0,[z1,z7,z2,z41,z5,z6,z92]),(0,[z1,z7,z2,z491,z3,z5,z6]),(1,[z70,z1,z7,z3,z5,z6]),(0,[z1,z7,z2,z404,z3,z5,z6]),(0,[z1,z7,z2,z492,z3,z5,z6]),(0,[z1,z7,z87,z2,z3,z5,z109]),(1,[z1,z7,z2,z116,z66,z6])],[(0,[z284,z7,z31,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z493,z5,z6]),(0,[z494,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z43,z2,z41,z5,z6]),(0,[z112,z1,z7,z2,z5,z64,z6])],[(0,[z1,z7,z2,z3,z495,z5,z6]),(0,[z1,z7,z2,z41,z5,z155,z6])],[(0,[z1,z22,z31,z2,z3,z5,z6]),(0,[z1,z7,z134,z2,z3,z5,z6])]],
   [[(1,[z147,z1,z2,z19,z5,z6]),(0,[z1,z7,z313,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z496,z5,z6]),(0,[z16,z1,z7,z2,z66,z5,z6]),(0,[z1,z7,z2,z3,z5,z497,z6]),(0,[z1,z7,z2,z3,z5,z498,z6])],[(0,[z499,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z500,z3,z5,z6]),(0,[z1,z7,z43,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z501,z6]),(0,[z502,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z373,z41,z5,z6]),(1,[z1,z7,z106,z3,z5,z6]),(1,[z156,z7,z2,z3,z5,z228]),(0,[z1,z7,z2,z3,z503,z5,z6])],[(0,[z504,z1,z7,z2,z3,z5,z6]),(0,[z144,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z248,z5,z6])],[(0,[z1,z7,z2,z505,z3,z5,z6]),(0,[z284,z7,z2,z3,z41,z5,z6]),(0,[z1,z7,z2,z506,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z507]),(1,[z508,z1,z7,z2,z5,z6])],[(0,[z509,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z510,z6]),(0,[z1,z7,z2,z511,z3,z5,z6]),(0,[z15,z1,z7,z2,z3,z5,z219]),(0,[z1,z7,z2,z3,z5,z512,z6]),(0,[z1,z513,z7,z2,z3,z5,z6])],[(0,[z16,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z514,z3,z5,z6])],[(0,[z0,z1,z7,z2,z456,z5,z6]),(0,[z1,z7,z377,z2,z3,z5,z6]),(0,[z1,z7,z3,z196,z5,z64,z6]),(0,[z144,z1,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z515,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z74,z5,z6]),(0,[z516,z1,z7,z2,z3,z5,z6]),(0,[z517,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z518,z3,z5,z6]),(0,[z519,z1,z7,z2,z3,z5,z6])],[(0,[z137,z1,z7,z2,z41,z5,z6]),(0,[z520,z1,z7,z2,z3,z5,z6]),(0,[z521,z1,z7,z2,z3,z5,z6]),(0,[z16,z1,z7,z3,z196,z5,z6]),(0,[z1,z7,z2,z3,z5,z522,z6])],[(1,[z0,z31,z2,z3,z5,z6]),(0,[z1,z7,z523,z2,z3,z5,z6]),(0,[z524,z1,z7,z2,z3,z5,z6]),(0,[z49,z1,z7,z2,z3,z5,z152]),(0,[z1,z7,z2,z24,z3,z5,z6])],[(0,[z525,z1,z7,z2,z3,z5,z6]),(0,[z107,z1,z7,z2,z3,z23,z6])],[(0,[z526,z1,z7,z2,z3,z5,z6]),(1,[z105,z7,z2,z3,z47,z6]),(0,[z1,z7,z2,z3,z5,z6,z527]),(0,[z1,z7,z2,z528,z3,z5,z6]),(0,[z529,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z530,z6]),(0,[z175,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z531,z3,z5,z6]),(0,[z7,z2,z3,z41,z5,z47,z6]),(0,[z1,z7,z2,z3,z395,z5,z6]),(0,[z1,z7,z2,z3,z532,z5,z6])]],
   [[(0,[z46,z68,z7,z2,z3,z5,z6]),(0,[z1,z7,z533,z2,z3,z5,z6]),(0,[z1,z7,z2,z534,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z535,z30]),(0,[z1,z7,z2,z116,z3,z5,z6]),(0,[z1,z7,z536,z2,z3,z5,z6])],[(0,[z130,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z537,z6]),(0,[z1,z7,z2,z538,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z539])],[(0,[z1,z7,z2,z41,z5,z6,z228]),(0,[z147,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z116,z5,z6]),(0,[z1,z7,z2,z3,z5,z540,z6]),(0,[z1,z7,z2,z3,z5,z218,z6]),(0,[z1,z7,z541,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z542,z5,z6])],[(1,[z50,z1,z43,z3,z5,z6]),(0,[z1,z7,z2,z543,z3,z5,z6])],[(0,[z46,z284,z1,z2,z3,z5,z6]),(0,[z544,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z545,z2,z3,z5,z6]),(0,[z50,z1,z7,z2,z382,z5,z6])],[(0,[z130,z1,z7,z2,z3,z5,z6]),(0,[z546,z1,z7,z2,z3,z5,z6]),(0,[z547,z1,z7,z2,z3,z5,z6]),(0,[z548,z1,z7,z2,z3,z5,z6]),(0,[z549,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z125,z5,z122])],[(0,[z1,z550,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z413,z6]),(0,[z1,z2,z19,z157,z3,z5,z6]),(0,[z1,z7,z2,z3,z148,z5,z6]),(0,[z156,z1,z7,z2,z3,z5,z131]),(0,[z551,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z552,z6]),(0,[z1,z7,z553,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z157,z5,z6]),(0,[z1,z7,z2,z19,z196,z5,z6]),(0,[z333,z1,z7,z2,z44,z3,z5]),(0,[z1,z7,z554,z2,z3,z5,z6]),(0,[z555,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z556,z3,z5,z6]),(0,[z144,z1,z7,z2,z3,z64,z6])]],
   [[(0,[z46,z1,z2,z3,z23,z5,z6]),(0,[z1,z7,z2,z3,z557,z5,z6]),(0,[z277,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z131,z6]),(0,[z1,z7,z2,z3,z5,z558,z6]),(0,[z559,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z560,z2,z3,z5,z6]),(0,[z561,z1,z7,z2,z3,z5,z6]),(0,[z562,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z288,z5,z6])],[(0,[z563,z1,z7,z2,z3,z5,z6]),(0,[z105,z68,z7,z2,z3,z5,z6]),(0,[z1,z59,z7,z87,z2,z3,z5])],[(0,[z564,z1,z7,z2,z3,z5,z6]),(0,[z565,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z566,z5,z6]),(0,[z1,z7,z2,z3,z5,z141,z6]),(0,[z1,z245,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z47,z6]),(0,[z1,z2,z3,z5,z34,z47,z6]),(0,[z567,z1,z7,z2,z3,z5,z6]),(0,[z20,z1,z2,z3,z5,z29,z6]),(0,[z1,z7,z2,z3,z5,z6,z568]),(0,[z1,z7,z2,z3,z5,z30,z122])],[(0,[z130,z1,z7,z3,z5,z65,z6]),(0,[z1,z11,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z97,z5,z6]),(0,[z1,z7,z2,z3,z5,z219,z6]),(0,[z1,z569,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z6,z6])],[(0,[z570,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z571,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z572,z6]),(0,[z1,z7,z2,z573,z3,z5,z6])],[(0,[z1,z7,z2,z19,z5,z65,z6]),(0,[z1,z574,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z575]),(0,[z1,z7,z2,z3,z5,z576,z6])]],
   [[(1,[z1,z7,z2,z178,z5,z6]),(1,[z1,z7,z2,z179,z5,z6]),(0,[z105,z1,z7,z2,z3,z5,z317]),(1,[z1,z7,z2,z294,z5,z6]),(0,[z1,z7,z2,z577,z3,z5,z6]),(0,[z49,z1,z301,z2,z3,z5,z6])],[(0,[z1,z7,z578,z2,z3,z5,z6])],[(0,[z1,z7,z31,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z579,z6]),(0,[z1,z7,z2,z3,z5,z6,z580])],[(0,[z1,z7,z2,z3,z5,z581,z6]),(0,[z1,z7,z2,z582,z41,z5,z6]),(0,[z1,z7,z2,z3,z583,z5,z6]),(0,[z114,z1,z7,z43,z3,z5,z6]),(0,[z584,z1,z7,z2,z3,z5,z6]),(0,[z15,z1,z7,z2,z3,z5,z189])],[(0,[z1,z7,z2,z3,z5,z5,z6]),(0,[z1,z7,z585,z2,z3,z5,z6]),(0,[z49,z114,z1,z7,z3,z5,z6]),(1,[z1,z7,z2,z58,z3,z5]),(0,[z1,z7,z586,z2,z3,z5,z6]),(0,[z587,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z3,z5,z6,z535]),(1,[z1,z7,z87,z3,z5,z65])],[(0,[z588,z1,z7,z2,z101,z3,z5]),(0,[z589,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z2,z382,z5,z6])],[(0,[z1,z7,z2,z3,z238,z5,z6]),(0,[z84,z277,z7,z2,z3,z5,z6]),(0,[z1,z590,z7,z2,z3,z5,z6]),(0,[z49,z1,z7,z2,z3,z5,z65]),(0,[z1,z7,z210,z2,z3,z5,z6]),(0,[z591,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z582,z3,z5,z6]),(0,[z1,z7,z2,z3,z200,z5,z6]),(0,[z1,z7,z2,z3,z66,z5,z6]),(0,[z1,z7,z592,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z5,z6,z593]),(0,[z7,z2,z19,z3,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z594,z6])],[(0,[z595,z1,z7,z2,z3,z5,z6]),(0,[z596,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z6,z597]),(0,[z598,z1,z7,z2,z3,z5,z6]),(0,[z599,z1,z7,z2,z3,z5,z6]),(0,[z1,z600,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z109]),(0,[z1,z7,z2,z3,z5,z6,z601]),(1,[z1,z7,z251,z3,z5,z6])],[(0,[z1,z7,z2,z261,z101,z3,z5]),(0,[z602,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z603])],[(1,[z1,z7,z2,z456,z5,z6]),(0,[z105,z1,z7,z2,z3,z127,z6]),(0,[z1,z7,z2,z3,z5,z604,z6]),(0,[z1,z7,z2,z3,z5,z605,z6]),(0,[z606,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z25,z152]),(0,[z1,z607,z7,z2,z3,z5,z6])],[(0,[z46,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z87,z2,z41,z5,z6]),(0,[z73,z1,z7,z2,z3,z5,z6]),(0,[z222,z1,z7,z2,z3,z6,z122])],[(1,[z588,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z3,z41,z5,z6]),(0,[z105,z7,z2,z3,z5,z47,z6])],[(0,[z68,z7,z2,z3,z127,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z608]),(0,[z1,z7,z2,z3,z5,z6,z609])]],
   [[(0,[z1,z7,z2,z106,z3,z5,z6]),(0,[z610,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z101,z41,z5,z6]),(0,[z1,z7,z2,z41,z196,z5,z6]),(0,[z611,z1,z7,z2,z3,z5,z6]),(0,[z20,z1,z2,z21,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z612,z6]),(0,[z1,z7,z87,z2,z3,z5,z6])],[(1,[z284,z7,z2,z41,z5,z6]),(0,[z1,z7,z90,z101,z3,z5,z6]),(0,[z94,z1,z7,z2,z3,z5,z6]),(1,[z7,z2,z19,z41,z5,z6]),(0,[z1,z7,z613,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z614,z6]),(0,[z1,z7,z2,z44,z19,z5,z6]),(0,[z156,z137,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z615,z6]),(0,[z616,z1,z7,z2,z3,z5,z6])],[(0,[z617,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z618]),(0,[z1,z7,z619,z2,z3,z5,z6]),(0,[z222,z1,z7,z2,z3,z5,z122])],[(0,[z1,z7,z2,z101,z3,z5,z6]),(0,[z1,z22,z7,z2,z41,z5,z6]),(0,[z84,z1,z7,z2,z41,z5,z6]),(0,[z156,z7,z2,z3,z5,z6,z228]),(0,[z1,z7,z2,z3,z5,z228,z122]),(0,[z1,z22,z7,z2,z3,z29,z6]),(1,[z16,z1,z7,z196,z5,z6])],[(0,[z1,z7,z2,z620,z3,z5,z6]),(0,[z621,z1,z7,z2,z3,z5,z6])],[(0,[z105,z1,z7,z2,z19,z5,z6]),(0,[z622,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z623,z2,z3,z5,z6]),(0,[z624,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z625])]],
   [[(0,[z126,z1,z7,z2,z41,z5,z6]),(0,[z626,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z627,z3,z5,z6]),(0,[z1,z7,z87,z3,z5,z65,z6])],[(0,[z1,z7,z2,z41,z5,z65,z6]),(0,[z1,z7,z2,z491,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z628,z6]),(0,[z629,z1,z7,z2,z3,z5,z6])],[(0,[z630,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z119,z2,z19,z5,z6]),(1,[z312,z7,z2,z3,z5,z6]),(0,[z1,z7,z631,z2,z3,z5,z6])],[(0,[z632,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z4,z5,z6]),(0,[z1,z7,z2,z3,z5,z633,z6]),(0,[z1,z7,z2,z634,z3,z5,z6]),(0,[z1,z7,z90,z3,z129,z5,z6]),(0,[z635,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z2,z5,z6,z281])],[(0,[z1,z7,z2,z3,z5,z636,z6]),(0,[z1,z7,z2,z116,z4,z5,z6]),(0,[z1,z2,z3,z5,z102,z6,z30]),(0,[z1,z7,z2,z3,z5,z637,z6]),(0,[z638,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z134,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z317,z6]),(0,[z639,z1,z7,z2,z3,z5,z6]),(0,[z15,z13,z1,z7,z2,z5,z6])],[(0,[z1,z7,z3,z5,z6,z364,z228]),(0,[z1,z7,z2,z3,z129,z5,z6]),(0,[z1,z7,z301,z2,z3,z5,z6]),(1,[z1,z7,z3,z5,z80,z6])],[(0,[z640,z1,z7,z2,z3,z5,z6]),(0,[z156,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z43,z2,z19,z5,z6]),(0,[z1,z641,z7,z2,z3,z5,z6]),(0,[z20,z1,z11,z2,z3,z5,z6]),(0,[z1,z642,z7,z2,z3,z5,z6]),(0,[z643,z1,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z19,z5,z25,z6]),(0,[z1,z7,z2,z3,z129,z5,z575]),(0,[z1,z7,z2,z3,z5,z152,z6])],[(1,[z0,z7,z2,z41,z5,z6]),(0,[z644,z1,z7,z2,z3,z5,z6]),(0,[z130,z1,z7,z2,z93,z5,z6]),(0,[z645,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z646,z6])],[(0,[z1,z7,z647,z2,z3,z5,z6])],[(0,[z126,z1,z7,z3,z5,z65,z6]),(0,[z156,z1,z7,z2,z3,z5,z6]),(0,[z137,z1,z7,z2,z3,z5,z228]),(0,[z648,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z649,z5,z6]),(0,[z107,z46,z1,z2,z3,z5,z6]),(1,[z1,z7,z2,z3,z5,z371]),(0,[z1,z650,z7,z2,z3,z5,z6]),(0,[z651,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z652]),(0,[z1,z7,z2,z5,z25,z6,z92]),(0,[z1,z7,z2,z3,z653,z5,z6])],[(0,[z284,z1,z2,z3,z5,z29,z6]),(0,[z144,z1,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z102,z152])],[(0,[z1,z7,z2,z3,z23,z5,z6]),(0,[z1,z7,z2,z3,z654,z5,z6]),(1,[z1,z7,z2,z3,z5,z575]),(0,[z1,z655,z7,z2,z3,z5,z6]),(0,[z656,z1,z7,z2,z3,z5,z6])],[(0,[z1,z657,z7,z2,z3,z5,z6]),(0,[z1,z7,z658,z2,z3,z5,z6]),(0,[z1,z7,z2,z659,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z116,z66,z5,z6]),(0,[z660,z1,z7,z2,z3,z5,z6])],[(0,[z661,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z662,z6]),(0,[z13,z1,z7,z2,z4,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z663])],[(0,[z1,z7,z2,z24,z41,z5,z6]),(0,[z525,z1,z7,z2,z19,z5,z6]),(1,[z137,z7,z2,z3,z5,z131]),(0,[z1,z7,z2,z4,z5,z120,z6]),(0,[z1,z7,z2,z3,z5,z664,z6]),(0,[z15,z1,z7,z2,z3,z120,z6])],[(0,[z70,z1,z7,z3,z5,z6,z228]),(0,[z1,z665,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z666,z6]),(0,[z1,z7,z2,z3,z5,z667,z6])],[(0,[z668,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z2,z332,z5,z6]),(0,[z137,z1,z7,z2,z19,z5,z6]),(0,[z1,z669,z7,z2,z3,z5,z6]),(0,[z670,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z671])],[(0,[z175,z1,z7,z2,z41,z5,z6]),(0,[z333,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z672,z2,z3,z5,z6]),(0,[z49,z1,z59,z7,z2,z3,z5]),(0,[z1,z7,z2,z3,z5,z6,z673])],[(0,[z126,z1,z7,z2,z209,z5,z6]),(0,[z1,z7,z2,z674,z3,z5,z6]),(0,[z508,z1,z7,z2,z3,z5,z6]),(1,[z1,z7,z149,z3,z5,z6])],[(0,[z1,z7,z2,z3,z675,z5,z6]),(0,[z1,z7,z2,z116,z41,z5,z6]),(0,[z1,z7,z2,z3,z676,z5,z6]),(0,[z68,z1,z7,z2,z3,z47,z6]),(0,[z1,z7,z677,z2,z3,z5,z6]),(0,[z107,z1,z7,z151,z3,z5,z6])]],
   [[(0,[z147,z1,z7,z2,z19,z5,z6]),(0,[z13,z1,z7,z2,z21,z5,z6]),(0,[z1,z7,z134,z2,z373,z5,z6]),(0,[z1,z7,z134,z373,z3,z5,z6])],[(0,[z1,z7,z678,z2,z3,z5,z6]),(0,[z13,z1,z7,z2,z24,z5,z6])],[(0,[z1,z7,z2,z3,z262,z5,z6]),(0,[z126,z7,z119,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z3,z5,z6]),(0,[z107,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z289,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z679]),(0,[z1,z7,z680,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z535])],[(0,[z130,z1,z7,z2,z19,z5,z6]),(1,[z1,z2,z157,z3,z5,z6]),(0,[z681,z1,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z216,z3,z5,z6]),(1,[z1,z7,z377,z3,z5,z6]),(0,[z175,z1,z7,z2,z3,z5,z30]),(0,[z1,z7,z2,z3,z5,z682,z6])],[(1,[z130,z7,z101,z3,z5,z6]),(0,[z1,z550,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z683,z41,z5,z6]),(0,[z1,z7,z2,z41,z4,z5,z6]),(0,[z312,z1,z7,z2,z3,z5,z6])],[(0,[z588,z1,z7,z2,z3,z5,z6]),(0,[z277,z1,z7,z2,z19,z5,z6]),(0,[z105,z1,z7,z2,z3,z5,z128]),(0,[z1,z7,z2,z684,z3,z5,z6]),(0,[z107,z1,z7,z2,z3,z5,z6]),(0,[z107,z1,z7,z2,z3,z5,z371]),(1,[z107,z1,z2,z3,z29,z6]),(1,[z1,z7,z2,z5,z268,z6])],[(0,[z1,z7,z685,z2,z3,z5,z6]),(0,[z1,z7,z2,z178,z3,z5,z6]),(0,[z686,z1,z7,z2,z3,z5,z6]),(0,[z687,z1,z7,z2,z3,z5,z6]),(0,[z1,z688,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z689]),(0,[z277,z1,z7,z2,z41,z5,z6]),(0,[z235,z1,z7,z2,z3,z5,z6]),(0,[z1,z690,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z5,z6,z691]),(0,[z68,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z251,z3,z5,z6]),(0,[z1,z7,z3,z125,z5,z80,z6])],[(0,[z1,z7,z2,z683,z3,z5,z6]),(0,[z1,z7,z2,z19,z5,z102,z6])],[(0,[z1,z7,z2,z3,z415,z5,z6]),(0,[z692,z1,z7,z2,z3,z5,z6]),(0,[z565,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z41,z5,z25,z6]),(0,[z84,z68,z7,z2,z3,z5,z6]),(0,[z50,z1,z43,z2,z3,z5,z6]),(0,[z1,z7,z693,z2,z3,z5,z6])],[(0,[z46,z284,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z6,z694]),(0,[z695,z1,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z324,z3,z5,z6]),(1,[z1,z22,z2,z3,z23,z6]),(0,[z508,z1,z7,z2,z5,z6,z122])],[(1,[z1,z7,z2,z191,z5,z6]),(0,[z1,z7,z2,z3,z5,z696,z6]),(0,[z1,z7,z2,z3,z5,z6,z697]),(0,[z1,z7,z698,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z29,z6]),(0,[z16,z1,z7,z2,z373,z5,z6])],[(0,[z1,z7,z2,z41,z432,z5,z6]),(0,[z1,z7,z244,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z699,z6]),(0,[z1,z7,z700,z2,z3,z5,z6])],[(0,[z0,z1,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z120,z6]),(0,[z1,z7,z2,z3,z5,z701,z6]),(0,[z1,z7,z2,z3,z5,z702,z6]),(0,[z1,z330,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z703,z6]),(0,[z704,z1,z7,z2,z3,z5,z6]),(0,[z1,z705,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z493,z5,z6]),(0,[z1,z7,z2,z19,z5,z6,z122]),(1,[z1,z7,z2,z255,z5,z6]),(1,[z135,z7,z2,z3,z5,z6]),(0,[z1,z7,z706,z2,z3,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z2,z41,z5,z47,z6]),(0,[z70,z1,z7,z19,z5,z6]),(0,[z1,z7,z19,z5,z6,z364]),(0,[z1,z7,z2,z707,z5,z6]),(1,[z1,z708,z3,z5,z6]),(0,[z1,z7,z2,z3,z709,z6]),(0,[z1,z7,z90,z3,z129,z575]),(0,[z1,z7,z2,z710,z5,z6]),(0,[z1,z7,z2,z711,z5,z6])],[(0,[z1,z7,z2,z712,z5,z6]),(0,[z312,z7,z2,z3,z5,z6]),(0,[z147,z2,z19,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z713]),(0,[z1,z7,z2,z714,z3,z5]),(0,[z1,z7,z2,z3,z5,z715]),(0,[z13,z1,z7,z2,z5,z663]),(0,[z16,z1,z210,z2,z5,z6]),(1,[z1,z7,z2,z3,z716])],[(0,[z717,z1,z7,z3,z5,z6]),(0,[z1,z7,z2,z5,z6,z718]),(0,[z1,z210,z2,z5,z25,z6])],[(0,[z7,z2,z719,z3,z5,z6]),(0,[z1,z2,z157,z5,z141,z6]),(0,[z1,z7,z2,z5,z6,z720]),(0,[z1,z2,z3,z5,z102,z721])],[(0,[z1,z2,z456,z4,z5,z6]),(0,[z1,z7,z2,z722,z5,z6]),(0,[z1,z7,z151,z3,z5,z371])],[(0,[z723,z31,z2,z3,z5,z6]),(0,[z130,z7,z101,z93,z5,z6]),(0,[z1,z2,z19,z157,z5,z6]),(0,[z7,z2,z288,z41,z47,z6]),(0,[z569,z7,z2,z19,z5,z6]),(0,[z1,z7,z3,z5,z724,z6]),(0,[z1,z7,z2,z3,z5,z725]),(0,[z726,z7,z2,z3,z5,z6]),(0,[z7,z2,z727,z3,z5,z6]),(0,[z1,z7,z3,z5,z80,z6]),(0,[z1,z7,z2,z728,z5,z6])],[(0,[z274,z7,z101,z3,z5,z6]),(0,[z1,z313,z2,z191,z5,z6]),(0,[z1,z7,z729,z3,z5,z6]),(0,[z1,z7,z2,z730,z120,z6])],[(0,[z1,z7,z2,z731,z5,z6]),(0,[z588,z1,z7,z2,z41,z5]),(0,[z1,z7,z2,z41,z5,z371]),(0,[z1,z7,z106,z19,z5,z6])]],
   [[(0,[z0,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z732,z5,z6]),(0,[z1,z7,z2,z733,z5,z6]),(0,[z1,z7,z2,z734,z5,z6]),(0,[z235,z1,z2,z735,z5,z6]),(0,[z736,z7,z2,z3,z5,z6]),(0,[z312,z7,z202,z3,z5,z6])],[(0,[z0,z31,z2,z238,z5,z6]),(0,[z1,z7,z2,z737,z5,z6]),(0,[z1,z7,z2,z738,z5,z6]),(0,[z1,z7,z2,z41,z5,z575]),(0,[z1,z7,z708,z3,z5,z6]),(0,[z1,z7,z2,z739,z5,z6])],[(0,[z1,z2,z178,z157,z5,z6]),(0,[z1,z7,z2,z3,z5,z740]),(0,[z1,z7,z2,z741,z5,z6]),(0,[z1,z7,z2,z3,z5,z742]),(0,[z156,z115,z7,z2,z3,z5]),(0,[z312,z210,z2,z3,z5,z6])],[(0,[z1,z7,z2,z3,z5,z6]),(0,[z1,z2,z743,z3,z5,z6]),(0,[z341,z7,z119,z3,z5,z6]),(0,[z7,z2,z35,z41,z5,z6]),(0,[z1,z7,z744,z41,z5,z6]),(0,[z84,z2,z19,z157,z5,z6]),(0,[z1,z2,z3,z5,z6,z745]),(0,[z1,z7,z2,z3,z5,z371]),(0,[z1,z7,z2,z746,z5,z6]),(0,[z1,z301,z2,z3,z5,z122])],[(0,[z1,z7,z2,z747,z5,z6]),(0,[z1,z7,z2,z748,z5,z6]),(0,[z1,z2,z749,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z750]),(0,[z549,z7,z2,z41,z5,z6]),(0,[z333,z1,z7,z2,z19,z5]),(0,[z1,z7,z751,z3,z5,z6]),(0,[z175,z230,z1,z3,z5,z30]),(0,[z1,z7,z752,z3,z5,z6])],[(0,[z137,z7,z2,z41,z5,z131]),(0,[z1,z7,z753,z3,z5,z6]),(0,[z1,z7,z87,z78,z3,z5]),(0,[z1,z7,z2,z3,z5,z575])],[(0,[z1,z7,z754,z3,z5,z6]),(0,[z52,z7,z2,z41,z5,z6]),(0,[z206,z7,z2,z41,z5,z6]),(0,[z16,z1,z7,z74,z5,z6]),(0,[z1,z7,z2,z3,z5,z755])],[(0,[z1,z7,z744,z3,z5,z6]),(0,[z1,z7,z2,z24,z5,z141]),(0,[z15,z1,z7,z2,z120,z6])]],
   [[(0,[z0,z31,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z756]),(0,[z7,z2,z41,z5,z6,z603]),(0,[z1,z244,z2,z157,z5,z6]),(0,[z1,z757,z2,z3,z5,z6]),(0,[z49,z1,z7,z492,z3,z5])],[(0,[z1,z7,z149,z41,z5,z6]),(0,[z70,z1,z7,z3,z5,z152]),(0,[z230,z1,z44,z3,z5,z6])],[(0,[z130,z7,z261,z101,z3,z5]),(0,[z1,z2,z41,z5,z34,z6]),(0,[z105,z7,z2,z19,z47,z6]),(0,[z502,z7,z2,z19,z5,z6]),(0,[z49,z1,z7,z3,z5,z237]),(0,[z107,z1,z2,z200,z29,z6]),(0,[z1,z7,z202,z3,z5,z6])],[(0,[z1,z7,z2,z332,z5,z6]),(0,[z318,z31,z2,z3,z5,z6]),(0,[z144,z1,z7,z268,z64,z6]),(1,[z1,z7,z3,z5,z758]),(0,[z1,z7,z2,z116,z730,z6])],[(0,[z312,z7,z2,z69,z5,z6]),(0,[z1,z210,z2,z3,z5,z6])],[(0,[z1,z7,z2,z759,z5,z6]),(0,[z760,z7,z2,z3,z5,z6]),(0,[z1,z7,z149,z3,z5,z6])],[(0,[z588,z126,z1,z7,z3,z5]),(0,[z1,z2,z157,z41,z5,z6]),(0,[z1,z7,z761,z3,z5,z6]),(0,[z107,z1,z151,z3,z29,z6]),(0,[z49,z1,z7,z3,z5,z250])],[(0,[z1,z7,z2,z762,z5,z6]),(0,[z1,z7,z2,z763,z5,z6]),(0,[z1,z7,z377,z41,z5,z6]),(0,[z1,z210,z2,z116,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z5,z764]),(0,[z1,z7,z2,z3,z765,z6]),(0,[z130,z7,z101,z41,z5,z6]),(0,[z1,z766,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z767])],[(0,[z1,z7,z2,z768,z5,z6]),(0,[z107,z1,z2,z41,z29,z6]),(0,[z1,z7,z3,z769,z5,z6]),(0,[z114,z1,z44,z3,z5,z6]),(0,[z1,z7,z2,z770,z5,z6]),(0,[z1,z7,z771,z3,z5,z6])],[(0,[z1,z7,z2,z772,z5,z6]),(0,[z130,z115,z7,z3,z5,z6]),(0,[z1,z7,z41,z5,z6,z364]),(0,[z300,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z288,z395,z6]),(0,[z1,z7,z2,z3,z5,z773]),(0,[z1,z7,z774,z3,z5,z6]),(0,[z775,z1,z7,z3,z5,z6]),(0,[z50,z1,z708,z3,z5,z6])],[(0,[z1,z7,z377,z3,z5,z6]),(0,[z49,z443,z1,z7,z3,z5]),(0,[z50,z1,z3,z5,z6,z99]),(0,[z1,z210,z202,z3,z5,z6])],[(0,[z130,z7,z101,z3,z5,z6]),(0,[z1,z7,z2,z5,z6,z776]),(0,[z204,z2,z3,z4,z5,z6]),(0,[z1,z22,z2,z3,z464,z6]),(0,[z437,z1,z2,z3,z5,z30])],[(0,[z1,z7,z777,z3,z5,z6]),(0,[z115,z7,z2,z41,z5,z6]),(0,[z1,z330,z251,z3,z5,z6])],[(0,[z204,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z69,z5,z6]),(0,[z1,z22,z2,z41,z23,z6]),(0,[z1,z7,z2,z5,z778,z6]),(0,[z1,z22,z2,z3,z709,z6])],[(0,[z1,z245,z2,z3,z5,z6]),(0,[z46,z284,z2,z41,z5,z6]),(0,[z588,z130,z1,z7,z3,z5]),(0,[z1,z7,z2,z779,z5,z6]),(0,[z1,z7,z90,z3,z5,z218]),(0,[z1,z7,z2,z780,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z5,z781]),(0,[z132,z7,z2,z782,z5,z6]),(0,[z1,z7,z2,z3,z783,z6]),(0,[z1,z210,z2,z5,z120,z6])],[(0,[z1,z7,z2,z3,z5,z784]),(0,[z1,z785,z2,z3,z5,z6]),(0,[z1,z786,z2,z3,z5,z6]),(0,[z222,z508,z1,z7,z2,z122])],[(0,[z787,z1,z7,z2,z3,z5]),(0,[z126,z7,z3,z5,z6,z442]),(0,[z135,z7,z2,z41,z5,z6]),(0,[z1,z2,z788,z3,z5,z6]),(0,[z107,z1,z2,z3,z29,z38]),(0,[z1,z789,z2,z3,z5,z6]),(0,[z508,z1,z7,z2,z5,z25])],[(0,[z790,z1,z7,z3,z5,z6]),(1,[z1,z7,z3,z791,z6])],[(0,[z331,z7,z2,z41,z5,z6]),(0,[z84,z7,z2,z69,z5,z6]),(0,[z333,z114,z1,z44,z3,z5]),(0,[z792,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z793,z5,z6]),(0,[z7,z2,z140,z41,z5,z6]),(0,[z794,z1,z7,z2,z5,z6]),(0,[z1,z7,z795,z3,z5,z6]),(0,[z1,z2,z796,z4,z5,z6])],[(0,[z1,z797,z2,z19,z5,z6]),(0,[z1,z7,z106,z3,z5,z128]),(0,[z798,z7,z2,z3,z5,z6])],[(0,[z1,z7,z799,z3,z5,z6]),(0,[z46,z2,z3,z5,z365,z6]),(0,[z800,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z801,z5,z6]),(0,[z7,z2,z41,z5,z497,z6]),(0,[z802,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z5,z25,z671])],[(0,[z46,z235,z2,z3,z5,z6]),(0,[z7,z2,z41,z5,z6,z652]),(0,[z1,z7,z87,z19,z5,z65]),(0,[z1,z7,z2,z66,z522,z6])],[(0,[z1,z7,z2,z803,z5,z6]),(0,[z1,z53,z2,z41,z5,z6]),(0,[z1,z7,z2,z344,z5,z141]),(0,[z529,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z804,z5,z6]),(0,[z1,z7,z2,z3,z5,z805]),(0,[z1,z7,z2,z3,z5,z721])],[(0,[z1,z2,z19,z788,z5,z6]),(0,[z1,z7,z2,z5,z6,z806]),(0,[z1,z7,z2,z807,z5,z6])],[(0,[z20,z0,z2,z41,z5,z6]),(0,[z1,z7,z2,z41,z5,z808]),(0,[z1,z809,z2,z41,z5,z6]),(0,[z1,z7,z2,z810,z5,z6]),(0,[z1,z7,z2,z811,z5,z6]),(0,[z1,z7,z2,z812,z5,z6]),(0,[z508,z1,z7,z2,z5,z92])],[(0,[z813,z1,z7,z2,z5,z6]),(0,[z814,z1,z2,z3,z5,z6]),(0,[z388,z7,z2,z41,z5,z6]),(0,[z235,z7,z2,z41,z5,z6]),(0,[z1,z815,z2,z19,z5,z6]),(0,[z816,z7,z2,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z758]),(0,[z312,z330,z2,z3,z5,z6])],[(0,[z7,z2,z817,z41,z5,z6]),(0,[z49,z704,z1,z7,z3,z5]),(1,[z235,z2,z41,z5,z6])],[(0,[z1,z7,z2,z818,z5,z6]),(0,[z1,z7,z2,z216,z5,z25]),(0,[z1,z7,z2,z19,z5,z819]),(0,[z147,z1,z2,z4,z5,z6]),(0,[z1,z7,z251,z19,z5,z6]),(0,[z1,z245,z377,z3,z5,z6]),(0,[z49,z1,z7,z634,z3,z5]),(0,[z135,z210,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z3,z820,z6]),(0,[z1,z7,z2,z3,z5,z821]),(0,[z132,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z822,z5,z6]),(0,[z1,z809,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z823]),(0,[z1,z7,z2,z3,z5,z824]),(0,[z132,z7,z2,z3,z5,z371]),(0,[z77,z1,z7,z2,z3,z122])],[(0,[z1,z313,z2,z3,z5,z6]),(0,[z46,z1,z2,z200,z5,z6]),(0,[z1,z7,z825,z41,z5,z6]),(0,[z525,z1,z2,z157,z5,z6]),(0,[z105,z7,z2,z3,z47,z128]),(0,[z50,z1,z428,z3,z5,z6]),(0,[z1,z301,z3,z5,z64,z6])],[(0,[z1,z7,z2,z148,z5,z6]),(0,[z1,z7,z3,z791,z64,z6]),(0,[z135,z7,z2,z3,z5,z219])],[(0,[z1,z7,z2,z3,z826,z6]),(0,[z827,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z828,z5,z6]),(0,[z1,z7,z2,z829,z5,z6]),(0,[z1,z830,z2,z3,z5,z6])],[(0,[z68,z7,z2,z332,z5,z6]),(0,[z1,z7,z719,z3,z5,z6]),(0,[z107,z1,z2,z324,z29,z6])],[(0,[z525,z7,z2,z41,z5,z6]),(0,[z284,z2,z683,z41,z5,z6]),(0,[z1,z7,z825,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z831]),(0,[z1,z655,z2,z4,z5,z6]),(0,[z1,z7,z2,z832,z5,z6])],[(0,[z1,z7,z833,z3,z5,z6]),(0,[z1,z7,z2,z834,z5,z6]),(0,[z1,z7,z2,z48,z5,z6]),(0,[z1,z7,z2,z835,z5,z6]),(0,[z1,z7,z836,z41,z5,z6]),(0,[z147,z1,z2,z21,z5,z6]),(0,[z837,z1,z2,z69,z5,z6]),(0,[z1,z7,z90,z3,z174,z6]),(0,[z13,z1,z7,z2,z5,z92])],[(0,[z1,z7,z2,z93,z5,z6]),(0,[z277,z7,z2,z41,z5,z6]),(0,[z7,z2,z838,z3,z5,z6]),(0,[z602,z7,z2,z41,z5,z6]),(0,[z7,z2,z19,z838,z5,z6]),(0,[z84,z147,z2,z3,z5,z6]),(0,[z1,z245,z2,z191,z5,z6])]],
   [[(0,[z1,z7,z2,z839,z5,z6]),(0,[z213,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z840]),(0,[z1,z7,z2,z97,z5,z6]),(0,[z333,z1,z7,z2,z3,z5]),(0,[z508,z1,z7,z2,z5,z189])],[(0,[z1,z7,z841,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z716])],[(0,[z1,z7,z836,z3,z5,z6]),(0,[z1,z7,z2,z5,z6,z842])],[(0,[z588,z1,z7,z3,z5,z64]),(0,[z1,z7,z843,z3,z5,z6]),(0,[z107,z1,z339,z3,z29,z6])],[(0,[z584,z7,z2,z19,z5,z6]),(0,[z844,z1,z7,z3,z5,z6]),(0,[z1,z2,z796,z3,z5,z6]),(0,[z1,z7,z2,z845,z5,z6]),(0,[z1,z7,z846,z3,z5,z6])],[],[(0,[z1,z7,z90,z3,z368,z6]),(0,[z7,z2,z69,z41,z5,z6]),(0,[z1,z7,z847,z3,z5,z6]),(0,[z1,z7,z2,z848,z5,z6]),(0,[z16,z1,z7,z251,z5,z6])],[(0,[z312,z7,z2,z19,z5,z6])]],
   [[(0,[z1,z7,z2,z849,z5,z6]),(0,[z1,z7,z2,z58,z41,z5]),(0,[z1,z7,z2,z41,z5,z713]),(0,[z1,z7,z3,z5,z6,z850]),(0,[z1,z7,z2,z851,z5,z6]),(0,[z1,z7,z251,z3,z5,z219])],[(0,[z1,z313,z377,z3,z5,z6]),(0,[z1,z7,z2,z852,z5,z6]),(0,[z1,z7,z2,z3,z5,z853]),(0,[z1,z854,z2,z3,z5,z6]),(0,[z1,z7,z90,z3,z129,z6]),(0,[z15,z312,z7,z2,z120,z6])],[(0,[z1,z7,z2,z238,z5,z6]),(0,[z1,z7,z855,z3,z5,z6]),(0,[z147,z1,z2,z41,z5,z6]),(0,[z397,z7,z2,z41,z5,z6]),(0,[z1,z7,z377,z3,z5,z317]),(0,[z856,z1,z7,z2,z5,z6]),(0,[z13,z1,z7,z2,z5,z189])],[(0,[z1,z7,z151,z41,z5,z6]),(0,[z1,z7,z2,z200,z5,z6]),(0,[z1,z7,z857,z3,z5,z6]),(0,[z1,z7,z2,z200,z5,z371])],[(0,[z0,z2,z41,z4,z5,z6]),(0,[z7,z2,z19,z404,z5,z6]),(0,[z68,z7,z2,z191,z5,z6]),(0,[z1,z59,z2,z3,z5,z360])],[(0,[z1,z2,z19,z749,z5,z6]),(0,[z166,z7,z151,z3,z5,z6]),(0,[z1,z7,z858,z3,z5,z6])],[(0,[z147,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z859,z5,z6]),(0,[z7,z2,z41,z5,z17,z6]),(0,[z1,z7,z377,z48,z5,z6]),(0,[z137,z7,z2,z3,z5,z860]),(0,[z1,z7,z2,z291,z5,z6])],[(0,[z1,z7,z2,z861,z5,z6]),(0,[z1,z7,z151,z3,z5,z6]),(0,[z175,z1,z2,z3,z5,z721]),(0,[z49,z322,z1,z7,z3,z5])]],
   [[],[(0,[z318,z7,z2,z41,z5,z6]),(0,[z1,z7,z862,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z863]),(0,[z1,z864,z2,z3,z5,z6]),(0,[z1,z7,z2,z19,z5,z371]),(0,[z1,z7,z2,z865,z5,z6]),(0,[z1,z2,z3,z5,z721,z30])],[(0,[z1,z7,z2,z41,z5,z6]),(0,[z866,z1,z7,z3,z5,z6]),(0,[z1,z7,z2,z867,z5,z6]),(0,[z7,z119,z719,z3,z5,z6]),(0,[z1,z245,z2,z48,z5,z6]),(0,[z1,z7,z2,z191,z5,z317]),(0,[z105,z7,z2,z3,z868,z6]),(0,[z1,z145,z2,z21,z5,z6]),(0,[z1,z2,z3,z5,z709,z6]),(0,[z230,z1,z7,z3,z5,z122]),(0,[z1,z7,z2,z869,z5,z6]),(0,[z1,z7,z2,z870,z5,z6])],[(0,[z107,z1,z2,z3,z408,z6]),(0,[z1,z7,z2,z19,z5,z575]),(0,[z1,z7,z2,z871,z5,z6]),(0,[z872,z1,z7,z2,z3,z5]),(0,[z1,z7,z3,z873,z5,z6]),(0,[z1,z2,z874,z3,z5,z6]),(0,[z1,z7,z2,z875,z5,z6])],[(0,[z166,z7,z2,z3,z5,z6]),(0,[z0,z2,z41,z432,z5,z6]),(0,[z1,z876,z2,z3,z5,z6]),(0,[z877,z1,z7,z3,z5,z6]),(0,[z166,z7,z2,z3,z5,z371]),(0,[z1,z7,z2,z878,z5,z6])],[(0,[z1,z7,z2,z879,z5,z6]),(0,[z1,z7,z2,z880,z5,z6]),(0,[z1,z2,z69,z881,z5,z6]),(0,[z16,z1,z7,z882,z5,z6])],[(0,[z7,z295,z2,z41,z5,z6]),(0,[z1,z7,z19,z5,z6,z535]),(0,[z1,z757,z2,z19,z5,z6]),(0,[z1,z7,z2,z883,z5,z6]),(0,[z132,z22,z2,z3,z5,z6]),(0,[z884,z1,z2,z3,z5,z6])],[(0,[z84,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z41,z5,z756]),(0,[z1,z7,z2,z5,z6,z885]),(0,[z137,z7,z2,z19,z5,z131]),(0,[z105,z7,z106,z3,z47,z6])]],
   [[(0,[z1,z7,z2,z886,z5,z6]),(0,[z312,z7,z2,z3,z5,z219])],[(0,[z7,z2,z41,z5,z76,z6]),(0,[z1,z7,z202,z41,z5,z6]),(0,[z1,z7,z887,z3,z5,z6]),(0,[z7,z2,z404,z5,z25,z6]),(0,[z1,z7,z90,z3,z791,z6])],[(0,[z888,z1,z2,z3,z5,z6]),(0,[z546,z7,z2,z41,z5,z6]),(0,[z333,z1,z7,z90,z3,z5]),(0,[z135,z330,z2,z3,z5,z6])],[(0,[z588,z130,z7,z101,z3,z5]),(0,[z1,z210,z2,z41,z5,z6]),(0,[z1,z7,z149,z19,z5,z6]),(0,[z1,z574,z2,z4,z5,z6]),(0,[z1,z7,z2,z3,z5,z38]),(0,[z1,z7,z2,z889,z5,z6]),(0,[z1,z7,z2,z3,z730,z6])],[(0,[z1,z7,z890,z3,z5,z6]),(0,[z1,z7,z2,z891,z5,z6]),(0,[z1,z7,z892,z3,z5,z6]),(0,[z893,z1,z7,z2,z5,z6]),(0,[z1,z7,z2,z5,z894,z6]),(0,[z895,z7,z2,z3,z5,z6])],[(0,[z445,z7,z2,z41,z5,z6]),(0,[z1,z896,z2,z3,z5,z6]),(0,[z1,z7,z897,z3,z5,z6]),(0,[z1,z2,z4,z5,z411,z6]),(0,[z1,z7,z2,z3,z152,z716])],[(0,[z7,z82,z2,z19,z5,z6]),(0,[z222,z1,z7,z2,z19,z122]),(0,[z1,z7,z2,z3,z5,z860])],[(0,[z1,z7,z2,z898,z5,z6]),(0,[z68,z7,z2,z835,z5,z6]),(0,[z1,z7,z2,z899,z5,z6]),(0,[z900,z1,z7,z2,z5,z6]),(0,[z1,z7,z3,z5,z758,z109]),(0,[z15,z1,z7,z202,z120,z6])]],
   [[(0,[z1,z7,z2,z3,z5,z901]),(0,[z1,z7,z2,z3,z5,z902]),(0,[z114,z1,z44,z41,z5,z6]),(0,[z239,z1,z7,z415,z5,z6]),(0,[z1,z7,z2,z19,z5,z773]),(0,[z333,z1,z59,z2,z3,z5]),(0,[z1,z903,z2,z3,z5,z6])],[(0,[z126,z7,z119,z3,z5,z6]),(0,[z1,z7,z377,z19,z5,z6]),(0,[z651,z7,z2,z19,z5,z6]),(0,[z156,z7,z2,z3,z5,z860]),(0,[z1,z7,z2,z3,z5,z904]),(0,[z1,z905,z2,z3,z5,z6]),(1,[z1,z7,z2,z5,z906])],[(0,[z130,z7,z101,z19,z5,z6]),(0,[z1,z7,z3,z5,z6,z364]),(0,[z15,z1,z210,z2,z120,z6]),(0,[z1,z7,z2,z3,z5,z219])],[(0,[z107,z1,z2,z19,z29,z6]),(0,[z907,z1,z7,z2,z5,z6]),(0,[z1,z7,z2,z908,z5,z6])],[(0,[z909,z1,z2,z3,z5,z6]),(0,[z1,z313,z2,z48,z5,z6]),(0,[z1,z7,z2,z5,z910,z6]),(0,[z1,z7,z2,z3,z125,z716])],[(0,[z1,z7,z911,z3,z5,z6]),(0,[z204,z7,z2,z41,z5,z6]),(0,[z548,z1,z43,z3,z5,z6]),(0,[z1,z59,z2,z3,z5,z102]),(0,[z1,z7,z2,z912,z5,z6])],[(0,[z0,z86,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z913]),(0,[z1,z245,z2,z41,z5,z6]),(0,[z1,z914,z2,z3,z5,z6]),(0,[z70,z1,z7,z3,z5,z122]),(0,[z1,z7,z915,z2,z5,z6]),(0,[z1,z7,z3,z129,z791,z6]),(0,[z1,z7,z251,z3,z5,z189]),(0,[z15,z1,z7,z2,z120,z219])],[(0,[z1,z7,z2,z3,z916,z6]),(0,[z1,z7,z2,z917,z5,z6]),(0,[z1,z7,z2,z918,z5,z6])]],
   [[(0,[z1,z7,z919,z3,z5,z6]),(0,[z1,z7,z2,z209,z5,z6]),(0,[z1,z7,z2,z3,z5,z920]),(0,[z551,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z41,z5,z784]),(0,[z1,z22,z2,z19,z23,z6]),(0,[z1,z921,z2,z3,z5,z6]),(0,[z1,z7,z2,z922,z5,z6]),(0,[z175,z1,z3,z5,z535,z30])],[(0,[z1,z7,z2,z923,z5,z6]),(0,[z924,z1,z7,z2,z3,z5]),(0,[z7,z2,z19,z143,z5,z6]),(0,[z925,z1,z2,z3,z5,z6]),(0,[z926,z7,z2,z3,z5,z6]),(0,[z1,z515,z2,z4,z5,z6]),(0,[z1,z22,z2,z200,z5,z6]),(0,[z49,z1,z7,z3,z5,z109]),(0,[z1,z7,z202,z3,z5,z219])],[(0,[z1,z7,z2,z261,z19,z5]),(0,[z1,z7,z2,z927,z5,z6]),(0,[z68,z7,z2,z41,z47,z6]),(0,[z1,z7,z2,z928,z5,z6]),(0,[z929,z7,z2,z3,z5,z6]),(0,[z49,z50,z1,z59,z3,z5]),(0,[z1,z7,z2,z248,z5,z6]),(0,[z190,z1,z2,z21,z5,z6]),(0,[z930,z1,z2,z3,z5,z6])],[(0,[z1,z7,z931,z3,z5,z6]),(0,[z7,z2,z404,z3,z5,z6]),(0,[z7,z2,z332,z5,z47,z6]),(0,[z1,z7,z795,z19,z5,z6]),(0,[z1,z7,z882,z196,z5,z6]),(0,[z49,z1,z7,z3,z5,z454]),(0,[z1,z210,z2,z3,z5,z219])],[(0,[z1,z7,z2,z932,z5,z6]),(0,[z1,z7,z2,z933,z5,z6]),(0,[z135,z7,z2,z19,z5,z6]),(0,[z934,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z882,z5,z6]),(0,[z935,z7,z2,z3,z5,z6]),(0,[z1,z7,z149,z3,z5,z152])],[(0,[z181,z1,z7,z2,z3,z122]),(0,[z1,z7,z2,z324,z5,z6]),(0,[z936,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z324,z5,z371]),(0,[z1,z7,z3,z5,z64,z218])],[(0,[z284,z0,z2,z41,z5,z6]),(0,[z234,z1,z7,z2,z5,z96]),(0,[z333,z1,z2,z3,z5,z30]),(0,[z20,z2,z21,z404,z5,z6]),(0,[z7,z2,z404,z116,z5,z6]),(0,[z1,z7,z2,z5,z25,z189]),(0,[z1,z7,z3,z125,z80,z152])],[(0,[z1,z7,z3,z5,z6,z937]),(0,[z1,z938,z2,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z939])]],
   [[(0,[z1,z7,z41,z5,z6,z535]),(0,[z1,z7,z19,z5,z80,z6]),(0,[z132,z7,z2,z200,z5,z6]),(0,[z1,z2,z200,z5,z29,z6]),(0,[z112,z1,z7,z2,z5,z6])],[(0,[z1,z7,z940,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z941]),(0,[z1,z7,z942,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z943]),(0,[z1,z7,z2,z944,z5,z6])],[(0,[z175,z1,z2,z41,z5,z30]),(0,[z319,z1,z7,z2,z155,z6]),(0,[z1,z2,z19,z945,z5,z6])],[(0,[z126,z7,z119,z209,z5,z6]),(0,[z1,z7,z2,z3,z5,z946]),(0,[z68,z7,z2,z41,z5,z6]),(1,[z147,z2,z41,z5,z6]),(0,[z1,z301,z2,z41,z5,z6]),(0,[z230,z1,z7,z3,z5,z6]),(0,[z333,z1,z301,z2,z3,z5]),(0,[z112,z1,z7,z196,z5,z6])],[(0,[z1,z7,z2,z947,z3,z5]),(0,[z1,z7,z2,z3,z5,z948]),(0,[z1,z7,z2,z949,z5,z6]),(0,[z1,z53,z2,z19,z5,z6]),(0,[z1,z7,z339,z3,z5,z6]),(0,[z132,z7,z151,z3,z5,z6]),(0,[z1,z7,z339,z3,z5,z371]),(0,[z1,z2,z3,z23,z709,z6]),(0,[z1,z7,z134,z251,z5,z6]),(0,[z1,z7,z2,z950,z5,z6])],[(0,[z524,z7,z2,z41,z5,z6]),(0,[z1,z951,z2,z3,z5,z6]),(0,[z1,z2,z881,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z721])],[(0,[z1,z7,z2,z289,z5,z6]),(0,[z132,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z952,z5,z6]),(0,[z193,z7,z2,z19,z5,z6]),(0,[z1,z708,z44,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z953]),(0,[z175,z1,z2,z3,z5,z30]),(0,[z7,z2,z954,z3,z5,z6]),(0,[z312,z7,z2,z3,z5,z189])],[(0,[z7,z2,z41,z5,z187,z6]),(0,[z132,z7,z2,z41,z5,z6]),(0,[z1,z301,z2,z3,z5,z6]),(0,[z955,z7,z2,z3,z5,z6]),(0,[z7,z2,z404,z5,z120,z6])]],
   [[(0,[z1,z313,z2,z41,z5,z6])],[(0,[z1,z2,z178,z4,z5,z6]),(0,[z221,z1,z7,z3,z64,z6]),(0,[z1,z7,z2,z282,z5,z6]),(0,[z1,z7,z2,z41,z5,z317]),(0,[z1,z7,z41,z5,z956,z6])],[(1,[z7,z719,z3,z5,z6]),(0,[z1,z7,z2,z957,z5,z6]),(0,[z1,z2,z157,z5,z187,z6]),(0,[z1,z7,z2,z3,z5,z958]),(0,[z20,z204,z2,z21,z5,z6]),(0,[z1,z7,z2,z959,z5,z6])],[(0,[z1,z7,z2,z5,z960,z6]),(0,[z565,z1,z2,z683,z5,z6]),(0,[z606,z7,z2,z41,z5,z6]),(0,[z175,z1,z301,z2,z3,z5])],[(0,[z473,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z961,z5,z6]),(0,[z962,z1,z7,z41,z5,z6]),(0,[z7,z2,z3,z5,z860,z228]),(0,[z156,z7,z3,z5,z364,z228])],[(0,[z84,z147,z2,z19,z5,z6]),(0,[z1,z7,z2,z3,z5,z317]),(0,[z1,z7,z2,z3,z5,z963])],[(0,[z0,z7,z2,z817,z5,z6]),(0,[z7,z2,z838,z41,z5,z6]),(0,[z1,z330,z2,z41,z5,z6])],[(0,[z0,z31,z2,z456,z5,z6]),(0,[z1,z7,z2,z964,z5,z6]),(0,[z1,z7,z2,z3,z5,z965]),(0,[z156,z70,z1,z7,z3,z5]),(0,[z45,z1,z7,z2,z120,z6]),(0,[z1,z7,z2,z3,z5,z966])]],
   [[(0,[z0,z132,z2,z3,z5,z6]),(0,[z1,z7,z2,z967,z5,z6]),(0,[z322,z7,z2,z41,z5,z6]),(0,[z962,z1,z7,z3,z5,z6]),(0,[z1,z7,z377,z3,z5,z128]),(0,[z1,z7,z2,z3,z868,z6]),(0,[z50,z1,z43,z382,z5,z6]),(0,[z132,z7,z2,z3,z5,z38]),(0,[z1,z7,z3,z398,z64,z6]),(0,[z1,z7,z2,z3,z5,z189]),(0,[z968,z7,z2,z3,z5,z6]),(0,[z170,z1,z7,z2,z3,z122])],[(0,[z1,z7,z2,z3,z5,z969])],[(0,[z7,z2,z41,z5,z227,z6]),(0,[z2,z19,z157,z41,z5,z6]),(0,[z94,z1,z2,z157,z5,z6]),(0,[z105,z235,z2,z3,z47,z6]),(0,[z478,z1,z44,z3,z5,z6]),(0,[z1,z330,z2,z3,z5,z6])],[(0,[z1,z7,z2,z19,z5,z970]),(0,[z137,z7,z2,z573,z3,z5]),(0,[z15,z1,z330,z2,z120,z6])],[(0,[z1,z7,z19,z769,z5,z6]),(0,[z1,z7,z847,z19,z5,z6]),(0,[z1,z971,z2,z3,z5,z6]),(0,[z1,z7,z972,z3,z5,z6]),(0,[z15,z1,z7,z2,z120,z189])],[(0,[z1,z7,z2,z116,z493,z6]),(0,[z1,z7,z973,z3,z5,z6]),(0,[z166,z7,z2,z845,z5,z6]),(0,[z1,z7,z2,z974,z5,z6])],[(0,[z31,z2,z3,z5,z408,z6]),(0,[z1,z550,z2,z4,z5,z6])],[(0,[z1,z7,z975,z3,z5,z6]),(0,[z1,z7,z151,z200,z5,z6]),(0,[z976,z7,z2,z3,z5,z6]),(0,[z1,z7,z202,z3,z5,z189]),(0,[z1,z7,z2,z116,z66,z6])]],
   [[(0,[z1,z7,z977,z3,z5,z6]),(0,[z1,z7,z2,z191,z5,z128]),(0,[z525,z7,z2,z404,z5,z6]),(0,[z978,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z979,z5,z6])],[(0,[z7,z2,z41,z249,z5,z6]),(0,[z1,z980,z2,z3,z5,z6]),(0,[z1,z330,z202,z3,z5,z6])],[(0,[z130,z7,z719,z3,z5,z6]),(0,[z1,z7,z41,z5,z80,z6]),(0,[z20,z204,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z758]),(0,[z222,z1,z7,z2,z3,z122])],[(0,[z284,z550,z2,z41,z5,z6]),(0,[z144,z1,z7,z41,z64,z6]),(0,[z73,z1,z7,z2,z5,z92]),(0,[z45,z1,z2,z3,z29,z6]),(0,[z1,z2,z21,z796,z5,z6])],[(0,[z147,z1,z2,z19,z5,z6]),(0,[z981,z1,z7,z2,z5,z6]),(0,[z446,z7,z2,z41,z5,z6]),(0,[z7,z2,z19,z407,z5,z6]),(0,[z1,z7,z982,z3,z5,z6]),(0,[z166,z7,z2,z200,z5,z6]),(0,[z1,z7,z983,z2,z5,z6]),(0,[z1,z59,z2,z372,z3,z5]),(0,[z1,z984,z2,z3,z5,z6])],[(0,[z287,z0,z2,z3,z5,z6]),(0,[z1,z7,z151,z19,z5,z6])],[(0,[z588,z1,z7,z2,z19,z5]),(0,[z1,z550,z2,z432,z5,z6]),(0,[z1,z7,z2,z985,z5,z6]),(0,[z156,z7,z2,z3,z5,z228]),(0,[z7,z2,z986,z3,z5,z6]),(0,[z1,z330,z2,z3,z5,z219])],[(0,[z1,z2,z3,z5,z987,z6]),(0,[z1,z7,z2,z5,z6,z988]),(0,[z591,z7,z2,z3,z5,z131]),(0,[z1,z7,z2,z989,z3,z5]),(0,[z144,z1,z7,z3,z64,z6]),(0,[z1,z7,z3,z5,z791,z6]),(0,[z1,z7,z149,z3,z125,z152])]],
   [[(0,[z1,z7,z2,z3,z5,z990]),(0,[z1,z7,z2,z838,z5,z6]),(0,[z1,z991,z2,z3,z5,z6]),(0,[z7,z2,z3,z5,z6,z992]),(0,[z1,z7,z2,z5,z730,z6])],[(0,[z1,z245,z2,z3,z5,z317]),(0,[z993,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z3,z5,z994]),(0,[z995,z7,z2,z3,z5,z6]),(0,[z1,z7,z3,z5,z65,z758])],[(0,[z166,z7,z2,z19,z5,z6]),(0,[z132,z7,z2,z324,z5,z6])],[(0,[z166,z7,z2,z41,z5,z6]),(0,[z877,z1,z7,z41,z5,z6]),(0,[z1,z7,z2,z996,z5,z6]),(0,[z1,z7,z997,z3,z5,z6]),(0,[z1,z7,z2,z200,z5,z38]),(0,[z1,z7,z2,z66,z730,z6])],[(0,[z1,z7,z2,z19,z5,z6]),(0,[z20,z1,z2,z528,z5,z6])],[(0,[z459,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z998,z5,z6]),(0,[z333,z1,z7,z2,z41,z5]),(0,[z7,z2,z41,z5,z6,z302]),(0,[z11,z7,z2,z404,z5,z6]),(0,[z1,z7,z2,z999,z5,z6]),(0,[z1,z7,z2,z1000,z5,z6]),(0,[z13,z1,z7,z2,z5,z906])],[(0,[z1,z7,z2,z3,z5,z1001]),(0,[z1,z7,z2,z1002,z5,z6]),(0,[z1,z7,z2,z261,z3,z5]),(0,[z1,z7,z2,z3,z5,z1003]),(0,[z84,z7,z2,z838,z5,z6]),(0,[z7,z2,z19,z374,z5,z6]),(0,[z230,z1,z59,z7,z3,z5])],[(0,[z1,z7,z3,z5,z65,z689]),(0,[z7,z2,z41,z5,z6,z310]),(0,[z1,z7,z2,z3,z5,z1004]),(0,[z1,z7,z151,z3,z5,z38]),(0,[z1,z7,z2,z1005,z5,z6]),(0,[z222,z1,z7,z2,z281,z122])]],
   [[(0,[z1,z7,z2,z1006,z5,z6]),(0,[z1,z7,z2,z491,z493,z6]),(0,[z107,z1,z2,z3,z709,z6])],[(0,[z7,z2,z456,z41,z5,z6]),(0,[z1,z7,z2,z1007,z5,z6]),(0,[z1,z7,z2,z1008,z5,z6]),(0,[z660,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z38]),(0,[z7,z461,z2,z19,z5,z6]),(0,[z1009,z1,z7,z2,z5,z6]),(0,[z1,z7,z2,z3,z1010,z5]),(0,[z132,z7,z339,z3,z5,z6])],[(0,[z68,z7,z2,z3,z254,z6]),(0,[z49,z1,z7,z3,z5,z694]),(0,[z1,z1011,z2,z3,z5,z6]),(0,[z1,z7,z2,z41,z5,z38]),(0,[z1,z7,z2,z1012,z5,z6]),(0,[z1,z7,z3,z5,z1013,z6]),(0,[z1,z7,z2,z3,z791,z6])],[(0,[z1,z7,z202,z19,z5,z6]),(0,[z1,z7,z1014,z3,z5,z6]),(0,[z135,z7,z2,z3,z5,z189])],[(0,[z7,z719,z101,z3,z5,z6]),(0,[z1,z1015,z2,z3,z5,z6]),(1,[z7,z2,z3,z5,z860]),(0,[z166,z7,z2,z3,z5,z38]),(0,[z49,z1,z301,z3,z5,z109]),(0,[z1016,z7,z2,z3,z5,z6])],[(0,[z1,z2,z3,z5,z34,z6]),(0,[z1,z210,z2,z19,z5,z6]),(0,[z68,z313,z2,z3,z5,z6]),(0,[z1,z265,z2,z3,z5,z102])],[(0,[z1,z7,z2,z1017,z5,z6]),(0,[z230,z50,z1,z3,z5,z6]),(0,[z1018,z7,z2,z3,z5,z6]),(0,[z1,z7,z90,z3,z129,z218]),(0,[z1,z7,z2,z24,z5,z25])],[(0,[z1,z1019,z2,z3,z5,z6]),(0,[z126,z7,z119,z19,z5,z6]),(0,[z156,z70,z7,z3,z5,z228]),(0,[z50,z1,z43,z3,z5,z6]),(0,[z1020,z1,z7,z2,z3,z5]),(0,[z15,z1,z7,z251,z120,z6])]],
   [[(0,[z126,z7,z119,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z219]),(0,[z7,z2,z1021,z3,z5,z6]),(0,[z1,z59,z2,z291,z5,z102])],[(0,[z1,z7,z2,z41,z5,z219]),(0,[z1,z1022,z2,z3,z5,z6]),(0,[z132,z7,z2,z961,z5,z6]),(0,[z1,z7,z2,z1023,z5,z6])],[(0,[z1,z7,z2,z1024,z5,z6]),(0,[z114,z1,z44,z19,z5,z6]),(0,[z1,z7,z2,z1025,z5,z6]),(0,[z1,z7,z2,z1026,z5,z6]),(0,[z16,z1,z7,z229,z5,z6]),(0,[z1027,z7,z2,z3,z5,z6])],[(0,[z20,z1,z2,z456,z5,z6]),(0,[z1,z59,z2,z19,z5,z102]),(0,[z1,z313,z2,z3,z5,z317]),(0,[z1028,z1,z7,z2,z5,z6]),(0,[z1,z7,z3,z5,z1029,z6]),(0,[z1,z7,z2,z1030,z5,z6])],[(0,[z1,z7,z911,z41,z5,z6]),(0,[z1,z59,z2,z41,z5,z102])],[(0,[z235,z132,z2,z3,z5,z6]),(0,[z1031,z7,z2,z3,z5,z6])],[(0,[z1,z7,z2,z1032,z5,z6]),(0,[z1,z1033,z2,z41,z5,z6]),(0,[z147,z2,z3,z41,z5,z6]),(0,[z1,z921,z2,z19,z5,z6]),(0,[z1,z7,z106,z191,z5,z6]),(0,[z1,z7,z1034,z3,z5,z6]),(0,[z230,z1,z301,z3,z5,z6])],[(0,[z1,z7,z2,z41,z5,z218]),(0,[z204,z7,z2,z19,z5,z6]),(0,[z1,z7,z2,z1035,z5,z6])]],
   [[(0,[z1036,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z1037,z5,z6]),(0,[z49,z1,z7,z41,z5,z109]),(0,[z1,z245,z2,z19,z5,z6]),(0,[z1,z7,z2,z5,z1038,z6]),(0,[z1,z7,z2,z48,z5,z317]),(0,[z1,z7,z2,z3,z354,z152]),(0,[z333,z114,z1,z7,z3,z5]),(0,[z1,z7,z2,z1039,z5,z6]),(0,[z1040,z7,z2,z3,z5,z6]),(0,[z1041,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z1042,z6]),(0,[z1,z7,z2,z1043,z5,z6])],[(0,[z319,z1,z7,z2,z120,z6]),(0,[z105,z7,z377,z3,z47,z6]),(0,[z1,z2,z708,z3,z5,z6]),(0,[z1,z7,z2,z1044,z5,z6]),(0,[z1,z7,z151,z324,z5,z6]),(0,[z49,z629,z1,z7,z3,z5]),(0,[z13,z135,z7,z2,z5,z6])],[(0,[z7,z2,z404,z41,z5,z6]),(0,[z7,z2,z491,z41,z5,z6]),(0,[z1,z1033,z2,z3,z5,z6]),(0,[z1,z1045,z2,z3,z5,z6]),(0,[z1,z1046,z2,z3,z5,z6])],[(0,[z235,z1,z2,z41,z5,z6]),(0,[z313,z2,z3,z5,z47,z6]),(0,[z1,z7,z2,z1047,z5,z6]),(0,[z1,z59,z2,z3,z5,z721]),(0,[z1,z7,z2,z3,z5,z218])],[(0,[z1,z7,z2,z178,z5,z6]),(0,[z1,z7,z2,z179,z5,z6]),(0,[z1,z7,z2,z3,z1048,z5]),(0,[z7,z2,z41,z5,z6,z361]),(0,[z1,z1049,z2,z3,z5,z6]),(0,[z1,z7,z339,z200,z5,z6]),(0,[z1,z7,z2,z1050,z5,z6])],[(0,[z1,z7,z2,z1051,z5,z6]),(0,[z1,z7,z2,z1052,z5,z6]),(0,[z1,z797,z2,z3,z5,z6]),(0,[z1,z7,z2,z1053,z5,z6]),(0,[z1,z7,z2,z1054,z5,z6]),(0,[z681,z1,z7,z3,z64,z6]),(0,[z15,z1,z7,z2,z212,z6]),(0,[z1,z7,z2,z1055,z5,z6])],[(0,[z1,z7,z2,z3,z5,z1056]),(0,[z7,z2,z41,z5,z365,z6]),(0,[z137,z7,z2,z255,z5,z131]),(0,[z114,z1,z301,z3,z5,z6]),(0,[z166,z7,z2,z324,z5,z6])],[(0,[z235,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z41,z5,z128]),(0,[z7,z2,z835,z41,z5,z6]),(0,[z1057,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z1058,z5,z6]),(0,[z319,z7,z2,z41,z47,z6]),(0,[z1,z2,z41,z5,z1059,z6]),(0,[z1,z7,z2,z3,z5,z1060]),(0,[z1,z7,z2,z3,z5,z1061]),(0,[z1062,z7,z2,z3,z5,z6]),(0,[z1,z7,z87,z3,z5,z65])],[(0,[z105,z7,z2,z191,z47,z6]),(0,[z1,z7,z2,z1063,z5,z6])],[(0,[z1,z7,z2,z5,z1064,z6]),(0,[z230,z1,z7,z41,z5,z6]),(0,[z1,z7,z339,z19,z5,z6]),(0,[z137,z7,z2,z294,z5,z131]),(0,[z1,z7,z2,z297,z5,z25]),(0,[z1,z7,z87,z3,z5,z185])],[(0,[z1,z2,z3,z5,z1065,z6]),(0,[z7,z2,z506,z41,z5,z6]),(0,[z1,z7,z339,z41,z5,z6]),(0,[z7,z2,z659,z41,z5,z6]),(0,[z73,z1,z7,z2,z5,z42]),(0,[z1,z7,z2,z3,z5,z128]),(0,[z1,z7,z2,z1066,z5,z6])],[(0,[z723,z0,z2,z3,z5,z6]),(0,[z1,z815,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z1067]),(0,[z235,z2,z41,z5,z47,z6]),(0,[z513,z7,z2,z41,z5,z6]),(0,[z319,z7,z2,z3,z47,z6]),(0,[z175,z1,z2,z19,z5,z30]),(0,[z94,z1,z7,z74,z5,z6]),(0,[z616,z7,z2,z3,z5,z228])],[(0,[z1,z7,z2,z3,z5,z1068]),(0,[z1,z301,z2,z19,z5,z6]),(0,[z1,z7,z2,z1069,z5,z6]),(0,[z166,z7,z339,z3,z5,z6]),(0,[z1,z7,z2,z324,z5,z38])],[(0,[z1,z2,z491,z157,z5,z6]),(0,[z1,z7,z2,z1070,z5,z6]),(0,[z7,z134,z2,z404,z5,z6]),(0,[z7,z2,z1071,z3,z5,z6])],[(0,[z489,z31,z2,z3,z5,z6]),(0,[z1072,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z735,z5,z6]),(0,[z1073,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z456,z5,z6]),(0,[z1,z7,z87,z75,z3,z5]),(0,[z1074,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z1075,z5,z6])],[(0,[z565,z0,z2,z41,z5,z6]),(0,[z1,z7,z2,z262,z5,z6]),(0,[z1,z7,z2,z1076,z5,z6]),(0,[z1,z7,z2,z5,z1077,z6]),(0,[z1,z7,z2,z5,z25,z906]),(0,[z1,z7,z149,z3,z5,z122])],[(0,[z0,z2,z41,z23,z5,z6]),(0,[z588,z1,z7,z2,z3,z5]),(0,[z2,z41,z5,z34,z47,z6]),(0,[z7,z2,z41,z5,z392,z6]),(0,[z1,z313,z2,z19,z5,z6]),(0,[z1,z134,z2,z157,z5,z6]),(0,[z1078,z1,z2,z3,z5,z6]),(0,[z1,z7,z1079,z3,z5,z6])],[(0,[z1,z7,z2,z19,z5,z317])],[(0,[z1,z7,z339,z3,z5,z38]),(0,[z1,z59,z2,z248,z5,z102])],[(0,[z723,z1,z2,z3,z5,z6]),(0,[z130,z7,z101,z179,z5,z6]),(0,[z1,z7,z2,z3,z5,z1080]),(0,[z1,z7,z87,z3,z5,z758])],[(0,[z84,z7,z2,z456,z5,z6]),(0,[z1,z7,z2,z41,z5,z965]),(0,[z924,z1,z7,z2,z41,z5]),(0,[z1,z7,z2,z1081,z5,z6])],[(0,[z469,z1,z2,z3,z29,z6]),(0,[z7,z2,z41,z5,z207,z6]),(0,[z1,z7,z2,z41,z5,z189]),(0,[z84,z235,z2,z3,z5,z6]),(0,[z1082,z7,z2,z3,z5,z6])]],
   [[(0,[z1,z7,z2,z817,z5,z6]),(0,[z1,z7,z2,z3,z1083,z6]),(0,[z277,z7,z2,z838,z5,z6]),(0,[z88,z7,z2,z41,z5,z6]),(0,[z292,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z1084,z5,z6]),(0,[z13,z1,z2,z157,z5,z6]),(0,[z1,z330,z2,z19,z5,z6]),(0,[z1,z1085,z2,z3,z5,z6])],[(0,[z7,z2,z41,z5,z408,z6]),(0,[z132,z2,z3,z5,z29,z6]),(0,[z1,z7,z2,z1086,z5,z6]),(0,[z16,z1,z7,z196,z5,z6]),(0,[z1,z7,z90,z3,z483,z6])],[(0,[z0,z1,z2,z200,z5,z6]),(0,[z1,z971,z2,z19,z5,z6]),(0,[z1,z7,z972,z19,z5,z6]),(0,[z15,z1,z7,z2,z293,z6])],[(0,[z20,z1,z2,z157,z5,z6]),(0,[z235,z1,z2,z928,z5,z6])],[(0,[z1,z7,z2,z1087,z5,z6]),(0,[z126,z7,z119,z262,z5,z6]),(0,[z1,z7,z2,z41,z125,z152]),(0,[z547,z1,z2,z21,z5,z6]),(0,[z1,z7,z2,z116,z390,z6]),(0,[z135,z7,z134,z2,z5,z6])],[(0,[z1,z7,z2,z1088,z5,z6]),(0,[z1,z7,z41,z5,z6,z850]),(0,[z1089,z7,z2,z3,z5,z6])],[(0,[z1,z2,z3,z23,z316,z6]),(0,[z70,z1,z7,z41,z5,z6]),(0,[z1,z7,z2,z216,z5,z413]),(0,[z1090,z7,z2,z3,z5,z6]),(0,[z1,z301,z2,z3,z5,z152])],[(0,[z1,z7,z2,z58,z19,z5]),(0,[z1,z245,z2,z3,z5,z128]),(0,[z1,z7,z2,z5,z6,z281])]],
   [[(0,[z284,z2,z41,z5,z29,z6]),(0,[z1,z980,z2,z41,z5,z6]),(0,[z1,z11,z2,z157,z5,z6]),(0,[z1,z7,z2,z3,z125,z152])],[(0,[z333,z1,z7,z3,z5,z64]),(0,[z1091,z7,z2,z3,z5,z6]),(0,[z1,z7,z1092,z2,z5,z6]),(0,[z1,z7,z2,z3,z542,z152])],[(0,[z284,z7,z2,z332,z5,z6]),(0,[z70,z1,z7,z3,z5,z6])],[(0,[z204,z7,z2,z456,z5,z6]),(0,[z1,z7,z1093,z3,z5,z6]),(0,[z15,z1,z7,z2,z730,z6]),(0,[z1,z7,z2,z3,z5,z906])],[(0,[z1,z7,z2,z3,z1094,z6]),(0,[z156,z7,z2,z19,z5,z228]),(0,[z50,z1,z43,z97,z5,z6]),(0,[z13,z7,z2,z404,z5,z6]),(0,[z1,z7,z2,z1095,z5,z6]),(0,[z1,z210,z2,z3,z5,z189])],[(0,[z1,z7,z106,z41,z5,z6]),(0,[z156,z7,z2,z41,z5,z228]),(0,[z144,z1,z7,z19,z64,z6]),(0,[z1,z2,z157,z5,z25,z6]),(0,[z1,z7,z1096,z3,z5,z6]),(0,[z1,z7,z2,z5,z6,z1097]),(0,[z16,z135,z7,z2,z5,z6])],[(0,[z1,z7,z1098,z3,z5,z6]),(1,[z7,z2,z838,z5,z6]),(0,[z1,z1099,z7,z2,z5,z6]),(0,[z7,z2,z3,z5,z1100,z6]),(0,[z1,z7,z339,z324,z5,z6])],[(0,[z20,z7,z2,z404,z5,z6]),(0,[z1,z7,z2,z1101,z5,z6]),(0,[z1,z7,z2,z3,z5,z1102]),(0,[z49,z1,z7,z3,z5,z673]),(0,[z49,z1,z53,z3,z5,z109]),(0,[z1,z7,z3,z5,z1103,z6])]],
   [[(0,[z1104,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z1105,z5,z6]),(0,[z1,z7,z2,z1106,z5,z6]),(0,[z147,z1,z2,z157,z5,z6]),(0,[z1,z7,z2,z1107,z5,z6])],[(0,[z1,z7,z106,z3,z5,z6]),(0,[z425,z7,z2,z19,z5,z6]),(0,[z175,z230,z1,z7,z3,z5]),(0,[z1,z53,z2,z1108,z5,z6]),(0,[z135,z7,z251,z3,z5,z6])],[(0,[z1,z7,z2,z1109,z3,z5]),(0,[z1,z7,z2,z3,z5,z1110]),(0,[z1,z7,z2,z1111,z5,z6]),(0,[z1,z7,z2,z1112,z5,z6]),(0,[z1,z7,z2,z1113,z5,z6])],[(0,[z7,z2,z3,z5,z131,z860]),(0,[z1,z7,z3,z5,z384,z65]),(0,[z1,z7,z2,z3,z393,z152]),(0,[z49,z1,z7,z3,z5,z758]),(0,[z508,z1,z7,z2,z5,z6])],[(0,[z588,z1,z7,z90,z3,z5]),(0,[z147,z7,z2,z41,z5,z6])],[(0,[z1,z7,z2,z1114,z5,z6]),(0,[z621,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z1115,z5,z6]),(0,[z1116,z7,z2,z3,z5,z6]),(0,[z1117,z7,z2,z3,z5,z6]),(0,[z1,z1118,z2,z3,z5,z6]),(0,[z1119,z7,z2,z3,z5,z6])],[(0,[z0,z31,z2,z41,z5,z6]),(0,[z137,z7,z2,z3,z5,z131])],[(0,[z0,z2,z3,z432,z5,z6]),(0,[z1,z22,z2,z3,z57,z6]),(0,[z89,z7,z2,z41,z5,z6]),(0,[z147,z1,z2,z18,z5,z6]),(0,[z1,z7,z2,z3,z5,z1120]),(0,[z1121,z7,z2,z3,z5,z6]),(0,[z1122,z1,z7,z3,z5,z6]),(0,[z20,z1,z2,z796,z5,z6]),(0,[z1,z59,z301,z2,z3,z5]),(0,[z1,z7,z2,z1123,z5,z6])]],
   [[(0,[z105,z7,z2,z41,z47,z6]),(0,[z7,z2,z3,z5,z6,z860]),(0,[z114,z1,z58,z44,z3,z5]),(0,[z107,z132,z2,z3,z29,z6]),(0,[z1124,z1,z7,z2,z5,z6]),(0,[z1,z7,z1125,z3,z5,z6])],[(0,[z0,z7,z2,z332,z5,z6]),(0,[z107,z0,z2,z41,z5,z6]),(0,[z1,z313,z2,z3,z5,z128]),(0,[z1,z7,z2,z3,z5,z1126]),(0,[z1,z600,z2,z4,z5,z6]),(0,[z1,z2,z3,z709,z29,z6]),(0,[z135,z7,z2,z5,z25,z6]),(0,[z222,z1,z7,z2,z3,z716])],[(0,[z0,z31,z2,z3,z5,z6]),(0,[z20,z1,z2,z178,z5,z6]),(0,[z1,z1127,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z1128]),(0,[z1,z7,z2,z1129,z5,z6])],[(0,[z1,z7,z2,z1130,z5,z6]),(0,[z1,z7,z2,z1131,z5,z6])],[(0,[z163,z7,z2,z41,z5,z6]),(0,[z284,z22,z2,z41,z5,z6]),(0,[z105,z7,z2,z3,z47,z6]),(0,[z1,z11,z2,z796,z5,z6])],[(0,[z1,z7,z2,z1132,z5,z6]),(0,[z50,z1,z43,z19,z5,z6]),(0,[z1,z7,z2,z1133,z5,z6]),(0,[z1,z7,z1134,z3,z5,z6]),(0,[z1,z1135,z2,z3,z5,z6])],[(0,[z50,z1,z43,z41,z5,z6]),(0,[z1,z7,z2,z48,z5,z128]),(0,[z1,z7,z2,z5,z6,z1136]),(0,[z1,z7,z134,z5,z280,z6])],[(0,[z1,z2,z157,z3,z5,z6]),(0,[z222,z1,z7,z2,z41,z122]),(0,[z55,z1,z7,z2,z187,z6]),(0,[z1,z7,z2,z3,z5,z1137]),(0,[z114,z1,z708,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z1138]),(0,[z1139,z7,z2,z3,z5,z6]),(0,[z7,z2,z3,z5,z6,z1140]),(0,[z1,z7,z2,z3,z716,z122])]],
   [[(0,[z418,z7,z2,z41,z5,z6]),(0,[z1,z2,z3,z5,z6,z1141]),(0,[z1,z7,z2,z3,z433,z152]),(0,[z1142,z1,z7,z2,z5,z6])],[(0,[z126,z7,z719,z3,z5,z6]),(0,[z1,z7,z2,z1143,z5,z6])],[(0,[z1,z2,z157,z116,z5,z6]),(0,[z107,z1,z2,z3,z29,z6]),(0,[z107,z1,z2,z3,z29,z371]),(0,[z1,z7,z2,z5,z268,z6])],[(0,[z1,z7,z2,z1144,z5,z6]),(0,[z7,z2,z41,z5,z482,z6]),(1,[z1,z2,z796,z5,z6]),(0,[z15,z135,z7,z2,z120,z6]),(0,[z1,z7,z2,z1145,z5,z6])],[(0,[z16,z1,z2,z157,z5,z6]),(0,[z1,z7,z2,z1146,z5,z6])],[(0,[z1147,z1,z2,z3,z5,z6]),(0,[z1,z7,z2,z1148,z5,z6]),(0,[z909,z1,z2,z19,z5,z6]),(0,[z1,z245,z106,z3,z5,z6]),(0,[z1,z7,z3,z5,z65,z452]),(0,[z13,z1,z210,z2,z5,z6])],[(0,[z1,z7,z3,z5,z6,z1149]),(0,[z1,z1150,z2,z3,z5,z6]),(0,[z1,z1151,z2,z3,z5,z6]),(0,[z1152,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z1153,z5,z6]),(1,[z1,z2,z3,z5,z721]),(0,[z1,z1154,z2,z3,z5,z6])],[(0,[z1,z22,z2,z3,z23,z6])]],
   [[(0,[z1,z7,z2,z191,z5,z6]),(0,[z1155,z1,z7,z2,z5,z6]),(0,[z837,z1,z2,z3,z5,z6]),(0,[z1,z53,z2,z710,z5,z6]),(0,[z1,z2,z3,z5,z1156,z6]),(0,[z1,z7,z2,z66,z6,z507])],[(0,[z1,z7,z2,z3,z5,z1157]),(0,[z1,z7,z1158,z2,z5,z6]),(0,[z68,z7,z2,z41,z127,z6]),(0,[z1,z7,z2,z19,z5,z218]),(0,[z15,z1,z7,z2,z187,z6]),(0,[z1,z7,z3,z5,z6,z1159]),(0,[z1,z7,z2,z3,z5,z1160]),(0,[z1,z7,z3,z882,z5,z6]),(0,[z1,z7,z1161,z3,z5,z6])],[(0,[z49,z1,z7,z19,z5,z109]),(0,[z925,z1,z2,z19,z5,z6]),(0,[z166,z7,z2,z1044,z5,z6])],[(0,[z1162,z1,z7,z3,z5,z6]),(0,[z1,z7,z2,z261,z41,z5]),(0,[z1163,z1,z7,z2,z3,z5]),(0,[z1,z7,z2,z255,z5,z6]),(0,[z1,z7,z2,z41,z1048,z5]),(0,[z135,z7,z2,z3,z5,z6]),(0,[z1,z2,z157,z5,z120,z6]),(0,[z1,z1164,z2,z3,z5,z6]),(0,[z1,z7,z2,z1165,z5,z6]),(0,[z1,z7,z1166,z3,z5,z6])],[(0,[z1,z11,z2,z4,z5,z6]),(0,[z1,z7,z2,z796,z5,z6]),(0,[z1,z7,z1167,z3,z5,z6])],[(0,[z489,z7,z2,z41,z5,z6]),(0,[z235,z1,z2,z19,z5,z6]),(0,[z105,z2,z3,z34,z47,z6]),(0,[z1168,z7,z2,z3,z5,z6])],[(0,[z1,z1169,z2,z3,z5,z6]),(0,[z13,z1,z7,z2,z5,z96]),(0,[z20,z1,z2,z21,z5,z6]),(0,[z135,z7,z2,z116,z5,z6])],[(0,[z1,z7,z87,z41,z5,z65]),(0,[z1,z7,z2,z294,z5,z6]),(0,[z312,z7,z251,z3,z5,z6]),(0,[z1,z330,z2,z3,z5,z189])]],
   [[(0,[z1,z7,z2,z1170,z5,z6]),(0,[z1,z1171,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z1059,z6]),(0,[z105,z245,z2,z3,z47,z6]),(0,[z333,z50,z1,z7,z3,z5]),(0,[z1172,z7,z2,z3,z5,z6]),(0,[z16,z7,z2,z404,z5,z6])],[(0,[z1,z7,z2,z3,z5,z1173]),(0,[z1,z7,z2,z288,z66,z6]),(0,[z1,z7,z2,z19,z5,z128]),(0,[z156,z7,z2,z289,z5,z228]),(0,[z50,z1,z301,z3,z5,z6]),(0,[z1,z7,z2,z1108,z5,z6]),(1,[z1,z7,z2,z730,z6])],[(0,[z1,z7,z3,z5,z1174,z6]),(0,[z135,z7,z202,z3,z5,z6])],[(0,[z147,z1,z2,z456,z5,z6]),(0,[z1,z7,z2,z1175,z5,z6]),(0,[z1,z7,z1176,z3,z5,z6]),(0,[z1,z53,z2,z3,z5,z6]),(0,[z1,z7,z2,z58,z3,z5]),(0,[z1,z7,z3,z5,z6,z535]),(0,[z1,z301,z90,z3,z5,z6]),(0,[z1,z7,z1177,z3,z5,z6])],[(0,[z1,z7,z2,z1178,z5,z6]),(0,[z230,z1,z7,z19,z5,z6]),(0,[z7,z2,z191,z5,z47,z6]),(0,[z156,z7,z2,z282,z5,z228]),(0,[z1,z7,z2,z382,z5,z6]),(0,[z1,z7,z2,z1179,z5,z6]),(0,[z1,z7,z2,z3,z5,z1180]),(0,[z1,z1181,z2,z3,z5,z6]),(0,[z1,z7,z2,z171,z5,z25])],[(0,[z1,z7,z2,z3,z5,z808]),(0,[z1,z7,z251,z41,z5,z6]),(0,[z1072,z1,z2,z19,z5,z6]),(0,[z7,z2,z3,z868,z47,z6]),(0,[z1,z43,z708,z3,z5,z6]),(0,[z1,z650,z2,z4,z5,z6]),(0,[z1,z210,z134,z2,z5,z6])],[(0,[z20,z1,z2,z683,z5,z6]),(0,[z1,z951,z2,z19,z5,z6]),(0,[z107,z166,z2,z3,z29,z6])],[(0,[z46,z132,z2,z3,z5,z6]),(0,[z1,z7,z1182,z3,z5,z6]),(0,[z1,z313,z106,z3,z5,z6]),(0,[z144,z112,z1,z7,z64,z6]),(0,[z135,z7,z2,z5,z120,z6]),(0,[z1,z7,z2,z3,z6,z716])]],
   [[(0,[z1,z7,z106,z3,z5,z317]),(0,[z1,z7,z377,z191,z5,z6]),(0,[z1,z7,z2,z5,z1183,z6]),(0,[z112,z1,z7,z251,z5,z6]),(0,[z1,z7,z2,z3,z226,z122])],[(0,[z1,z7,z2,z3,z5,z819]),(0,[z1,z7,z251,z3,z5,z6]),(0,[z1,z7,z2,z5,z6,z906])],[(0,[z1,z7,z2,z1184,z5,z6]),(0,[z1,z7,z2,z3,z5,z1185]),(0,[z1,z7,z2,z3,z5,z1186]),(0,[z1,z7,z2,z1187,z5,z6]),(0,[z1,z7,z2,z5,z1188,z6]),(0,[z1189,z7,z2,z3,z5,z6]),(0,[z1,z7,z2,z3,z5,z1190])],[(0,[z1,z1191,z2,z3,z5,z6]),(0,[z1,z7,z2,z1192,z5,z6])],[(0,[z1,z7,z3,z5,z956,z6]),(0,[z1,z7,z106,z48,z5,z6]),(0,[z1,z7,z1193,z3,z5,z6]),(0,[z1,z7,z2,z1194,z5,z6]),(0,[z1,z2,z3,z5,z6,z1195]),(0,[z1,z7,z2,z5,z6,z1196])],[(0,[z1163,z1,z7,z2,z41,z5]),(0,[z670,z7,z2,z41,z5,z6]),(0,[z239,z1,z7,z196,z5,z6]),(0,[z234,z1,z2,z157,z5,z6]),(0,[z1,z7,z2,z1197,z5,z6]),(0,[z1,z1198,z7,z2,z5,z6])],[(0,[z1,z7,z2,z1199,z5,z6]),(0,[z335,z1,z7,z3,z64,z6])],[(0,[z235,z31,z2,z3,z5,z6]),(1,[z1,z2,z3,z709,z6]),(0,[z1,z7,z2,z24,z5,z906])]],
   [[(0,[z0,z52,z2,z3,z5,z6]),(0,[z1,z2,z19,z5,z34,z6]),(0,[z1,z7,z2,z1200,z5,z6]),(0,[z1,z1201,z2,z3,z5,z6]),(0,[z1,z7,z90,z3,z393,z6]),(0,[z1,z7,z2,z1202,z5,z6])],[(0,[z284,z7,z2,z41,z5,z6]),(0,[z469,z7,z2,z3,z47,z6]),(0,[z1,z7,z2,z1203,z5,z6]),(0,[z7,z2,z19,z41,z5,z6]),(0,[z1,z7,z2,z19,z5,z189]),(0,[z7,z2,z3,z5,z868,z6]),(0,[z49,z1,z7,z3,z5,z150]),(0,[z135,z7,z2,z491,z5,z6])],[(0,[z1,z7,z2,z3,z5,z970]),(0,[z1,z7,z2,z3,z5,z840]),(0,[z1,z2,z945,z3,z5,z6]),(0,[z105,z313,z2,z3,z47,z6]),(0,[z1,z7,z2,z1204,z5,z6]),(0,[z1,z7,z2,z1205,z5,z6]),(0,[z1,z210,z251,z3,z5,z6]),(0,[z1,z7,z2,z5,z906,z92])],[(0,[z1,z7,z2,z782,z5,z6]),(0,[z105,z7,z2,z3,z47,z317]),(0,[z1206,z7,z2,z3,z5,z6])],[(0,[z723,z7,z2,z3,z5,z6]),(0,[z1,z7,z3,z5,z6,z1207]),(0,[z70,z137,z1,z7,z3,z5]),(0,[z1,z7,z3,z5,z1208,z6]),(0,[z112,z1,z7,z134,z5,z6])],[(0,[z312,z7,z2,z41,z5,z6]),(0,[z414,z7,z2,z41,z5,z6]),(0,[z1,z7,z2,z3,z5,z1209]),(0,[z1,z7,z2,z3,z5,z1210]),(0,[z1,z7,z2,z1211,z5,z6]),(0,[z230,z1,z7,z3,z5,z152])],[(0,[z1,z7,z2,z19,z125,z152]),(0,[z1,z7,z3,z5,z6,z1212]),(0,[z144,z1,z7,z3,z791,z6])],[(0,[z1,z7,z1213,z3,z5,z6]),(0,[z235,z2,z3,z41,z5,z6]),(0,[z105,z7,z2,z48,z47,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 521).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1046).take 201) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1247)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [521, 525, 201] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 102).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 208).take 48).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [102, 106, 48] = true :=
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

end PEqualNP.Outside.L_meta_40229

theorem PEqualNP.Outside.L_meta_40229 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272614016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272614016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40229.solve