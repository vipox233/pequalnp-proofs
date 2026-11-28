import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45924

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
  Nat.testBit (4276677288 * 2 ^ 32 + 4007701152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x80010b012c4308ab#64 ++ 0x4000858096218455#64 ++ 0x7c031f0ffcc71fff#64 ++ 0xbe018f87fe638fff#64 : BitVec 256),
   (0x040c657495596599#64 ++ 0x820632ba4aacb2cc#64 ++ 0xfc1ce7f49f79e599#64 ++ 0x7e0e73fa4fbcf2cc#64 : BitVec 256),
   (0x00e0b0b8c380b614#64 ++ 0x0070585c61c05b0a#64 ++ 0xfbe0f8f8e381fe1e#64 ++ 0xfdf07c7c71c0ff0f#64 : BitVec 256),
   (0x017600de03ac0740#64 ++ 0x00bb006f01d603a0#64 ++ 0xdfff00ff03fe07e1#64 ++ 0xefff807f81ff03f0#64 : BitVec 256),
   (0x0bbbdf0002f7d800#64 ++ 0x05ddef80017bec00#64 ++ 0xefffff0003fff801#64 ++ 0xf7ffff8001fffc00#64 : BitVec 256),
   (0x13dffeeff8000000#64 ++ 0x09efff77fc000000#64 ++ 0xf3fffffffc000001#64 ++ 0xf9fffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe0f8f8e381fe1e 0xfdf07c7c71c0ff0f

def z1 : W := mkw 0x01160046002c0140 0x008b0023001600a0 0x041f0007007e01e1 0x020f8003803f00f0

def z2 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdfff00ff03fe07e1 0xefff807f81ff03f0

def z3 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1ce7f49f79e599 0x7e0e73fa4fbcf2cc

def z4 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff0003fff801 0xf7ffff8001fffc00

def z5 : W := mkw 0x13dffeeff82c0140 0x09efff77fc1600a0 0xf7fffffffc7e01e1 0xfbfffffffe3f00f0

def z6 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x7c031f0ffcc71fff 0xbe018f87fe638fff

def z7 : W := mkw 0x057e45de17fd47c9 0x82bf22ef0bfea3e4 0xdfff07ff1ffe07e1 0xefff83ff8fff03f0

def z8 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fffffffc000001 0xf9fffffffe000000

def z9 : W := mkw 0x00e0b0a8c280b214 0x007058546140590a 0x23e0f808e081fa1e 0x91f07c047040fd0f

def z10 : W := mkw 0x0004005401080500 0x0002002a00840280 0xdc1c00f403780581 0x6e0e007a01bc02c0

def z11 : W := mkw 0x0408652094516099 0x820432904a28b04c 0x2000e7009c01e018 0x100073804e00f00c

def z12 : W := mkw 0x0bbbdf1003ffdf40 0x05ddef8801ffefa0 0xefffff0003ffffe1 0xf7ffff8001fffff0

def z13 : W := mkw 0x006000980380b614 0x0030004c01c05b0a 0xdbe000f80381fe1e 0xedf0007c01c0ff0f

def z14 : W := mkw 0x84096f21bc5368bb 0xc204b790de29b45d 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z15 : W := mkw 0x0400011005596599 0x8200008802acb2cc 0x0c0000000379e598 0x0600000001bcf2cc

def z16 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff0fffffffff 0xffffff87ffffffff

def z17 : W := mkw 0x840d4f453c5b49ab 0xc206a7a29e2da4d5 0x041f07071c7e01e1 0x020f83838e3f00f0

def z18 : W := mkw 0x1b1f4f4738774800 0x0d8fa7a39c3ba400 0x041f07071c7e0001 0x020f83838e3f0000

def z19 : W := mkw 0x0172008a02a40240 0x00b9004501520120 0x03e3000b00860260 0x81f1800580430130

def z20 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0x83fce0000338e000 0x41fe7000019c7000

def z21 : W := mkw 0x0400010004516099 0x820000800228b04c 0x000000000001e018 0x000000000000f00c

def z22 : W := mkw 0x1bdfffeff853d800 0x0deffff7fc29ec00 0xf3fffffffc01f801 0xf9fffffffe00fc00

def z23 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c03000f00c607e1 0xae018007806303f0

def z24 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xa3e0f8f0e301f81e 0x51f07c787180fc0f

def z25 : W := mkw 0x8bb39b012ee798ab 0x45d9cd809773cc55 0x7fe31f0ffcc71fff 0xbff18f87fe638fff

def z26 : W := mkw 0x0bbbde0002a69800 0x05ddef0001534c00 0xe3ffff0000861801 0xf1ffff8000430c00

def z27 : W := mkw 0x0004207481082510 0x0002103a40841288 0xfc1ce0f48379e599 0x7e0e707a41bcf2cc

def z28 : W := mkw 0x81f7bbffefefbfff 0x40fbddfff7f7dfff 0xffffffffffffffff 0xffffffffffffffff

def z29 : W := mkw 0x0bffdfde03ffdf40 0x05ffefef01ffefa0 0xffffffff03ffffe1 0xffffffff81fffff0

def z30 : W := mkw 0x80000100044308ab 0x4000008002218455 0x0c00000000c71ffe 0x0600000000638fff

def z31 : W := mkw 0x93dfffeffc4308ab 0x49effff7fe218455 0xfffffffffcc71fff 0xfffffffffe638fff

def z32 : W := mkw 0x131f4e4738000000 0x098fa7239c000000 0x001f07071c000001 0x000f83838e000000

def z33 : W := mkw 0x13dffefff9080500 0x09efff7ffc840280 0xffffffffff780581 0xffffffffffbc02c0

def z34 : W := mkw 0x015e64ee90000000 0x00af327748000000 0xf3ffe7ff9c000001 0xf9fff3ffce000000

def z35 : W := mkw 0x055e65fe95596599 0x82af32ff4aacb2cc 0xffffe7ff9f79e599 0xfffff3ffcfbcf2cc

def z36 : W := mkw 0x0bb39a0002a69800 0x05d9cd0001534c00 0x03e3180000861800 0x81f18c0000430c00

def z37 : W := mkw 0x0fbfff7497fffd99 0x87dfffba4bfffecc 0xfffffff49ffffd99 0xfffffffa4ffffecc

def z38 : W := mkw 0x0404207495082599 0x8202103a4a8412cc 0x100000f49c000598 0x0800007a4e0002cc

def z39 : W := mkw 0x0820010002f7d800 0x04100080017bec00 0x0c00000003fff800 0x0600000001fffc00

def z40 : W := mkw 0x104420eff8000000 0x08221077fc000000 0x100000fffc000000 0x0800007ffe000000

def z41 : W := mkw 0x0bb2900002a49000 0x05d9480001524800 0x03e0000000000000 0x01f0000000000000

def z42 : W := mkw 0x0132000002a40000 0x0099000001520000 0x83fc000003380000 0x41fe0000019c0000

def z43 : W := mkw 0x0000001001080740 0x00000008008403a0 0x00000000000007e0 0x00000000000003f0

def z44 : W := mkw 0x000c646490000000 0x0006323248000000 0xf01ce7f49c000001 0x780e73fa4e000000

def z45 : W := mkw 0x015600ce00000000 0x00ab006700000000 0xd3ff00ff00000001 0xe9ff807f80000000

def z46 : W := mkw 0x01570acf28000000 0x00ab856794000000 0xf3ff1ffffc000001 0xf9ff8ffffe000000

def z47 : W := mkw 0x0408451005596599 0x8204228802acb2cc 0xec1ce7000379e599 0x760e738001bcf2cc

def z48 : W := mkw 0x104420eed0000000 0x0822107768000000 0x000000f000000000 0x0000007800000000

def z49 : W := mkw 0x01f2b0bac3a4b654 0x00f9585d61d25b2a 0xfbe3f8fbe387fe7e 0xfdf1fc7df1c3ff3f

def z50 : W := mkw 0x1289fe21f8000000 0x0944ff10fc000000 0x2000ff00fc000000 0x10007f807e000000

def z51 : W := mkw 0x0008450000514000 0x000422800028a000 0xec1ce7000379e001 0x760e738001bcf000

def z52 : W := mkw 0x039bde0000000000 0x01cdef0000000000 0xe3ffff0000000001 0xf1ffff8000000000

def z53 : W := mkw 0x135f4ecf38000000 0x09afa7679c000000 0xd3ff07ff1c000001 0xe9ff83ff8e000000

def z54 : W := mkw 0x006020b8c380b614 0x0030105c61c05b0a 0x180000f8e381fe1e 0x0c00007c71c0ff0f

def z55 : W := mkw 0x01f6b0fec3acb754 0x00fb587f61d65baa 0xfffff8ffe3ffffff 0xfffffc7ff1ffffff

def z56 : W := mkw 0x8081bb21ec43b8bf 0x4040dd90f621dc5f 0x7c03ff0ffcc7ffff 0xbe01ff87fe63ffff

def z57 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x040307071c4601e1 0x020183838e2300f0

def z58 : W := mkw 0x80e1bbb9efc3bebf 0x4070dddcf7e1df5f 0xffe3ffffffc7ffff 0xfff1ffffffe3ffff

def z59 : W := mkw 0x04ecf5fcd7d9f79d 0x82767afe6becfbce 0xfffce7f49f79e599 0x7ffe73fa4fbcf2cc

def z60 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc1c000003780001 0x660e000001bc0000

def z61 : W := mkw 0x0bb39b0002f7d800 0x05d9cd80017bec00 0x0fe3180003fff800 0x87f18c0001fffc00

def z62 : W := mkw 0x12c9fea9f8000000 0x0964ff54fc000000 0xf3e0fff8fc000000 0xf9f07ffc7e000000

def z63 : W := mkw 0x93d39b8b6c4308ab 0x49e9cdc5b6218455 0x7fe31f0ffcc71fff 0xbff18f87fe638fff

def z64 : W := mkw 0x81770adf2bae0f62 0x40bb856f95d707b1 0xdfff18ff63fe1fe7 0xefff8c7fb1ff0ff3

def z65 : W := mkw 0x00010a0128000000 0x0000850094000000 0x70031f0ffc000001 0xb8018f87fe000000

def z66 : W := mkw 0x00c0b0a8c0000000 0x0060585460000000 0xf3e0f8f8e0000000 0xf9f07c7c70000000

def z67 : W := mkw 0x0020001003ac0740 0x0010000801d603a0 0x0c00000003fe07e0 0x0600000001ff03f0

def z68 : W := mkw 0x13fffefffbac0740 0x09ffff7ffdd603a0 0xfffffffffffe07e1 0xffffffffffff03f0

def z69 : W := mkw 0x000c647491080500 0x0006323a48840280 0xfc1ce7f49f780581 0x7e0e73fa4fbc02c0

def z70 : W := mkw 0x800001012c4100ab 0x4000008096208055 0x7c00070ffc4107ff 0x3e000387fe2083ff

def z71 : W := mkw 0x13d39a8b68000000 0x09e9cd45b4000000 0x03e3180b60000000 0x81f18c05b0000000

def z72 : W := mkw 0x8b1b4f012c7748ab 0x458da780963ba455 0x041f07071c7e01e1 0x020f83838e3f00f0

def z73 : W := mkw 0x0bfbffb8c3f7fe14 0x05fdffdc61fbff0a 0xfffffff8e3fffe1f 0xfffffffc71ffff0f

def z74 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xffe3f8ffe3c7ffff 0xfff1fc7ff1e3ffff

def z75 : W := mkw 0x8020011007ef0feb 0x4010008803f787f5 0x0c00000003ff1ffe 0x0600000001ff8fff

def z76 : W := mkw 0x81770bdf2fef0feb 0x40bb85ef97f787f5 0xffff1fffffff1fff 0xffff8fffffff8fff

def z77 : W := mkw 0x840d6f75bd5b6dbb 0xc206b7badeadb6dd 0xfc1fffffffffffff 0xfe0fffffffffffff

def z78 : W := mkw 0x0bfbffb8c3f7fe14 0x05fdffdc61fbff0a 0xeffffff003fff801 0xf7fffff801fffc00

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x20001800e001181e 0x10000c0070008c0f

def z80 : W := mkw 0x0bfbffa8c2f7d800 0x05fdffd4617bec00 0xfffffff8e3fff801 0xfffffffc71fffc00

def z81 : W := mkw 0x81330b012ee708ab 0x4099858097738455 0xffff1f0fffff1fff 0xffff8f87ffff8fff

def z82 : W := mkw 0x004400de01080740 0x0022006f008403a0 0x100000ff000007e0 0x0800007f800003f0

def z83 : W := mkw 0x0a89df000053d800 0x0544ef800029ec00 0x2000ff000001f800 0x10007f800000fc00

def z84 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfffffffffcc607e1 0xfffffffffe6303f0

def z85 : W := mkw 0x04e0b1b8c7d9f79d 0x827058dc63ecfbce 0xffe0f8f8e3f9ff9e 0xfff07c7c71fcffcf

def z86 : W := mkw 0x000c656494410089 0x000632b24a208044 0xfc1ce7f49c410599 0x7e0e73fa4e2082cc

def z87 : W := mkw 0x01f6b0fec3acb754 0x00fb587f61d65baa 0x83fce0f00338e000 0x41fe7078019c7000

def z88 : W := mkw 0x040c454414594189 0x820622a20a2ca0c4 0x041c07041c780181 0x020e03820e3c00c0

def z89 : W := mkw 0x04ecf5fcd7d9f79d 0x82767afe6becfbce 0xfffcfffcfff9ff9f 0xfffe7ffe7ffcffcf

def z90 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfbfffffffc811e1f 0xfdfffffffe408f0f

def z91 : W := mkw 0x0f1f4f44147f4989 0x878fa7a20a3fa4c4 0x041f07041c7e0181 0x020f83820e3f00c0

def z92 : W := mkw 0x00e0908842809204 0x0070484421404902 0x7be01808e0811e1e 0xbdf00c0470408f0f

def z93 : W := mkw 0x839bdf012c4308ab 0x41cdef8096218455 0xffffff0ffcc71fff 0xffffff87fe638fff

def z94 : W := mkw 0x0132000002a40000 0x0099000001520000 0xdfff000f03fe07e1 0xefff800781ff03f0

def z95 : W := mkw 0x00c0b0a8c0000000 0x0060585460000000 0xfbe0f8f8e0811e1e 0xfdf07c7c70408f0f

def z96 : W := mkw 0x017620fe83ac2750 0x00bb107f41d613a8 0xffffe0ff83ffe7f9 0xfffff07fc1fff3fc

def z97 : W := mkw 0x004400ce00000000 0x0022006700000000 0x100000ff00000000 0x0800007f80000000

def z98 : W := mkw 0x0080b020c000b014 0x004058106000580a 0x2000f800e001f81e 0x10007c007000fc0f

def z99 : W := mkw 0x13dffeeff800b014 0x09efff77fc00580a 0xf3fffffffc01f81f 0xf9fffffffe00fc0f

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x78001808e0811e1e 0xbc000c0470408f0f

def z101 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x83ffe7f71c000001 0x41fff3fb8e000000

def z102 : W := mkw 0x93ffffffffef0feb 0x49fffffffff787f5 0xffffffffffff1fff 0xffffffffffff8fff

def z103 : W := mkw 0x0bbad50002f7d800 0x05dd6a80017bec00 0x8ffce00003fff800 0x47fe700001fffc00

def z104 : W := mkw 0x002000100380b614 0x0010000801c05b0a 0x080000000381fe1e 0x0400000001c0ff0f

def z105 : W := mkw 0x00e0909803809600 0x0070484c01c04b00 0xfbe0f8f80381fe00 0xfdf07c7c01c0ff00

def z106 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x6c031f00fcc7181f 0xb6018f807e638c0f

def z107 : W := mkw 0x0008440000000000 0x0004220000000000 0xe01ce70000000001 0x700e738000000000

def z108 : W := mkw 0x004400de01080740 0x0022006f008403a0 0x5c0300ff00c607e1 0xae01807f806303f0

def z109 : W := mkw 0x00a0900002809000 0x0050480001404800 0xebe0f8000381f800 0xf5f07c0001c0fc00

def z110 : W := mkw 0x80010a0128020822 0x4000850094010411 0x0003180b60861a66 0x80018c05b0430d33

def z111 : W := mkw 0x93dffeeff8020822 0x49efff77fc010411 0xf3fffffffc861a67 0xf9fffffffe430d33

def z112 : W := mkw 0x00c0b0b8c1002614 0x0060585c6080130a 0xf3e0f8f8e000061e 0xf9f07c7c7000030f

def z113 : W := mkw 0x0bbbff3083f7fc10 0x05ddff9841fbfe08 0xfffffff083fffc19 0xfffffff841fffe0c

def z114 : W := mkw 0x000c455401594500 0x000622aa00aca280 0xfc1ce7f40379e581 0x7e0e73fa01bcf2c0

def z115 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x83fc00f003380000 0x41fe0078019c0000

def z116 : W := mkw 0x1bffffeffaf7d800 0x0dfffff7fd7bec00 0xfffffffffffff801 0xfffffffffffffc00

def z117 : W := mkw 0x0060009803800600 0x0030004c01c00300 0xdbe000f803800600 0xedf0007c01c00300

def z118 : W := mkw 0x9289ff21fc4308ab 0x4944ff90fe218455 0x7c03ff0ffcc71fff 0xbe01ff87fe638fff

def z119 : W := mkw 0x00a8d50002d1d000 0x00546a800168e800 0xeffcff0003f9f801 0xf7fe7f8001fcfc00

def z120 : W := mkw 0x004020b8c1002614 0x0020105c6080130a 0x100000f8e000061e 0x0800007c7000030f

def z121 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x83e0e0f00300e000 0x41f0707801807000

def z122 : W := mkw 0x00010b0000430800 0x0000858000218400 0x20001f0000011800 0x10000f8000008c00

def z123 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0xd3ffe0ff00000001 0xe9fff07f80000000

def z124 : W := mkw 0x1bfef4eed2b4d000 0x0dff7a77695a6800 0x83fce0f00338e000 0x41fe7078019c7000

def z125 : W := mkw 0x840c6574955b6dbb 0xc20632ba4aadb6dd 0xfc1ce7f49fffffff 0x7e0e73fa4fffffff

def z126 : W := mkw 0x13fffefffb800600 0x09ffff7ffdc00300 0xfbffffffff800601 0xfdffffffffc00300

def z127 : W := mkw 0x03bbde0002809000 0x01ddef0001404800 0xebffff000381f801 0xf5ffff8001c0fc00

def z128 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0x83fce0f000000000 0x41fe707800000000

def z129 : W := mkw 0x0404217495596599 0x820210ba4aacb2cc 0x1c0000f49f79e598 0x0e00007a4fbcf2cc

def z130 : W := mkw 0x0000001001002410 0x0000000800801208 0x080000000301e418 0x040000000180f20c

def z131 : W := mkw 0x84edfffdffdbffbf 0xc276fffeffedffdf 0xffffffffffffffff 0xffffffffffffffff

def z132 : W := mkw 0x00e0908842809204 0x0070484421404902 0x03e0180860801a06 0x81f00c0430400d03

def z133 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff08e3fffe1f 0xffffff8471ffff0f

def z134 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000000c607e0 0x06000000006303f0

def z135 : W := mkw 0x0400001005082599 0x82000008028412cc 0x0000000000000598 0x00000000000002cc

def z136 : W := mkw 0x040d6f75bd596599 0x8206b7badeacb2cc 0xfc1fffffff79e599 0xfe0fffffffbcf2cc

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000180860801a06 0x80000c0430400d03

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0x5003000f00000001 0xa801800780000000

def z139 : W := mkw 0x0bbbde0002b6d800 0x05ddef00015b6c00 0x83fff80003bef800 0xc1fffc0001df7c00

def z140 : W := mkw 0x017600ce02a40000 0x00bb006701520000 0xdfff00ff03fe0001 0xefff807f81ff0000

def z141 : W := mkw 0x00010b0000430800 0x0000858000218400 0x6c031f0000c71801 0xb6018f8000638c00

def z142 : W := mkw 0x0400010004594189 0x82000080022ca0c4 0x0400000000780180 0x02000000003c00c0

def z143 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xa01ce7f09f39e018 0x500e73f84f9cf00c

def z144 : W := mkw 0x0828450002f7d800 0x04142280017bec00 0xec1ce70003fff801 0x760e738001fffc00

def z145 : W := mkw 0x040c647491186510 0x8206323a488c3288 0x801ce0f00338e000 0x400e7078019c7000

def z146 : W := mkw 0x0008450004514089 0x000422800228a044 0xfc1ce7049f79e599 0x7e0e73824fbcf2cc

def z147 : W := mkw 0x0b9bdf000077d800 0x05cdef80003bec00 0x241fff00007ff801 0x120fff80003ffc00

def z148 : W := mkw 0x0bfaf4b8c3b4f614 0x05fd7a5c61da7b0a 0x83fce0f00338e000 0x41fe7078019c7000

def z149 : W := mkw 0x0008653081516410 0x0004329840a8b208 0xfc1ce7f08379e419 0x7e0e73f841bcf20c

def z150 : W := mkw 0x8b1b4f012c7748ab 0x458da780963ba455 0x7c1f1f0ffcff1fff 0xbe0f8f87fe7f8fff

def z151 : W := mkw 0x017600de03acb754 0x00bb006f01d65baa 0xdfff00ff03ffffff 0xefff807f81ffffff

def z152 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xebfcf80003b9f800 0xf5fe7c0001dcfc00

def z153 : W := mkw 0x17dfffeffc516099 0x8beffff7fe28b04c 0xf3fffffffc01e019 0xf9fffffffe00f00c

def z154 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x13e018f8e0801e1e 0x89f00c7c70400f0f

def z155 : W := mkw 0x0112000000000000 0x0089000000000000 0xc3ff000000000001 0xe1ff800000000000

def z156 : W := mkw 0x00010a0128000000 0x0000850094000000 0x0003180b60000000 0x80018c05b0000000

def z157 : W := mkw 0x040c647495186599 0x8206323a4a8c32cc 0x901ce0f49f38e598 0x480e707a4f9c72cc

def z158 : W := mkw 0x0000202080002010 0x0000101040001008 0x2000e0008001e018 0x100070004000f00c

def z159 : W := mkw 0x13dfdecf78000000 0x09efef67bc000000 0x03ff1f0f7c000001 0x81ff8f87be000000

def z160 : W := mkw 0x0000000000000000 0x0000000000000000 0x6800180000811800 0xb4000c0000408c00

def z161 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x87ff00f7037e01e1 0x43ff807b81bf00f0

def z162 : W := mkw 0x03939a0000000000 0x01c9cd0000000000 0x03e3180000000000 0x81f18c0000000000

def z163 : W := mkw 0x8bbbdf012af7d822 0x45ddef80957bec11 0xefffff0b63fffa67 0xf7ffff85b1fffd33

def z164 : W := mkw 0x0404217495492599 0x820210ba4aa492cc 0x7c0007f49c410599 0x3e0003fa4e2082cc

def z165 : W := mkw 0x0040009801000600 0x0020004c00800300 0x100000f800000600 0x0800007c00000300

def z166 : W := mkw 0x12094e0138000000 0x0904a7009c000000 0x000007001c000000 0x000003800e000000

def z167 : W := mkw 0x13fffefffb80b614 0x09ffff7ffdc05b0a 0xfbffffffff81fe1f 0xfdffffffffc0ff0f

def z168 : W := mkw 0x006020b8c3802614 0x0030105c61c0130a 0xdbe000f8e380061e 0xedf0007c71c0030f

def z169 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x13e300ff008607e0 0x89f1807f804303f0

def z170 : W := mkw 0x0bf3bab8c3a6be14 0x05f9dd5c61d35f0a 0xfbe3f8f8e387fe1e 0xfdf1fc7c71c3ff0f

def z171 : W := mkw 0x0b1b4f0000774800 0x058da780003ba400 0x041f0700007e0001 0x020f8380003f0000

def z172 : W := mkw 0x0b9bdf0000774800 0x05cdef80003ba400 0xe7ffff00007e0001 0xf3ffff80003f0000

def z173 : W := mkw 0x057e65fe97fd67d9 0x82bf32ff4bfeb3ec 0xffffe7ff9fffe7f9 0xfffff3ffcffff3fc

def z174 : W := mkw 0x00e4b0fec388b754 0x0072587f61c45baa 0xfbe0f8ffe381fffe 0xfdf07c7ff1c0ffff

def z175 : W := mkw 0x00c0b0a8c000b014 0x006058546000580a 0xf3e0f8f8e001f81e 0xf9f07c7c7000fc0f

def z176 : W := mkw 0x0404207491082510 0x8202103a48841288 0x000000f000000000 0x0000007800000000

def z177 : W := mkw 0x13d39a8b68000000 0x09e9cd45b4000000 0x73e31f0ffc000001 0xb9f18f87fe000000

def z178 : W := mkw 0x80010b00044308ab 0x4000858002218455 0x6c031f0000c71fff 0xb6018f8000638fff

def z179 : W := mkw 0x0bfaf4b8c3b4f614 0x05fd7a5c61da7b0a 0xfbfcf8f8e3b9fe1e 0xfdfe7c7c71dcff0f

def z180 : W := mkw 0x0b1a440000344000 0x058d2200001a2000 0x001c000000380000 0x000e0000001c0000

def z181 : W := mkw 0x0000203081002410 0x0000101840801208 0xf800e0f08301e418 0x7c0070784180f20c

def z182 : W := mkw 0x0004005401080500 0x0002002a00840280 0xdc1f00ff03fe07e1 0xee0f807f81ff03f0

def z183 : W := mkw 0x00010a0000000000 0x0000850000000000 0x60031f0000000001 0xb0018f8000000000

def z184 : W := mkw 0x0172009a03a40640 0x00b9004d01d20320 0xdbe300fb03860660 0xedf1807d81c30330

def z185 : W := mkw 0x0fbfff7493fffd10 0x87dfffba49fffe88 0xeffffff003fff801 0xf7fffff801fffc00

def z186 : W := mkw 0x004420fec1082754 0x0022107f608413aa 0x100000ffe00007fe 0x0800007ff00003ff

def z187 : W := mkw 0x040c455415596599 0x820622aa0aacb2cc 0x0c1c07041f79e599 0x060e03820fbcf2cc

def z188 : W := mkw 0x17dffffffd596599 0x8beffffffeacb2cc 0xffffffffff79e599 0xffffffffffbcf2cc

def z189 : W := mkw 0x0000010004410089 0x0000008002208044 0x7c0007049c410599 0x3e0003824e2082cc

def z190 : W := mkw 0x0bbbdf0006f7d889 0x05ddef80037bec44 0xffffff049ffffd99 0xffffff824ffffecc

def z191 : W := mkw 0x039ad40000000000 0x01cd6a0000000000 0x83fce00000000000 0x41fe700000000000

def z192 : W := mkw 0x13fef4fed380b614 0x09ff7a7f69c05b0a 0xfbfcf8f8e381fe1e 0xfdfe7c7c71c0ff0f

def z193 : W := mkw 0x0008642090000000 0x0004321048000000 0x2000e7009c000000 0x100073804e000000

def z194 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x2c001f00fcc71ffe 0x16000f807e638fff

def z195 : W := mkw 0x039ffe6490000000 0x01cfff3248000000 0xf3fffff49c000001 0xf9fffffa4e000000

def z196 : W := mkw 0x1040008b68000000 0x08200045b4000000 0x0000000b60000000 0x00000005b0000000

def z197 : W := mkw 0x040c647495082599 0x8206323a4a8412cc 0xf01ce7f49c000599 0x780e73fa4e0002cc

def z198 : W := mkw 0x0112000000240000 0x0089000000120000 0x041f0000007e0001 0x020f8000003f0000

def z199 : W := mkw 0x00a0900002809000 0x0050480001404800 0x83e0e0000300e000 0x41f0700001807000

def z200 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x841ce7f41f78e181 0x420e73fa0fbc70c0

def z201 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xcfffe00003fee001 0xe7fff00001ff7000

def z202 : W := mkw 0x0000010000514000 0x000000800028a000 0x0c0000000379e000 0x0600000001bcf000

def z203 : W := mkw 0x051e6576957d65d9 0x828f32bb4abeb2ec 0xfc1fe7f79f7fe5f9 0x7e0ff3fbcfbff2fc

def z204 : W := mkw 0x80a19b012ec398ab 0x4050cd809761cc55 0xffe3ff0fffc7ffff 0xfff1ff87ffe3ffff

def z205 : W := mkw 0x84042075bd0825bb 0xc202103ade8412dd 0x100000fffc0007fe 0x0800007ffe0003ff

def z206 : W := mkw 0x81170b472c6f09eb 0x408b85a3963784f5 0x041f07071c7e01e1 0x020f83838e3f00f0

def z207 : W := mkw 0x0400011005596599 0x8200008802acb2cc 0x7c0007049f79e599 0x3e0003824fbcf2cc

def z208 : W := mkw 0x13dfffeff8514000 0x09effff7fc28a000 0xffffffffff79e001 0xffffffffffbcf000

def z209 : W := mkw 0x017600ce02ac0340 0x00bb0067015601a0 0x07ff000f00fe03e1 0x83ff8007807f01f0

def z210 : W := mkw 0x144420fffd082599 0x8a22107ffe8412cc 0x100000fffc000598 0x0800007ffe0002cc

def z211 : W := mkw 0x0172008a02a40240 0x00b9004501520120 0x03e0000000000000 0x01f0000000000000

def z212 : W := mkw 0x0a094f0000534800 0x0504a7800029a400 0x0000070000000000 0x0000038000000000

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x7800000080010418 0x3c0000004000820c

def z214 : W := mkw 0x13dffefff9002614 0x09efff7ffc80130a 0xf3fffffffc00061f 0xf9fffffffe00030f

def z215 : W := mkw 0x0136005603ac0740 0x009b002b01d603a0 0x0c1f000703fe07e1 0x060f800381ff03f0

def z216 : W := mkw 0x00010a0128000000 0x0000850094000000 0x78031f0ffc811e1f 0xbc018f87fe408f0f

def z217 : W := mkw 0x00a0b0308380b410 0x0050581841c05a08 0xfbe0f8f08381fc18 0xfdf07c7841c0fe0c

def z218 : W := mkw 0x00e0b1b8c7c1b69d 0x007058dc63e0db4e 0xffe0fffcffc1ff9f 0xfff07ffe7fe0ffcf

def z219 : W := mkw 0x13def4eff8000000 0x09ef7a77fc000000 0x93fce0fffc000000 0x49fe707ffe000000

def z220 : W := mkw 0x00ccf4ecd0000000 0x00667a7668000000 0xf3fcfffcfc000001 0xf9fe7ffe7e000000

def z221 : W := mkw 0x0172008a02a40240 0x00b9004501520120 0xcfff000b03fe0261 0xe7ff800581ff0130

def z222 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x93fc00ff033807e0 0x49fe007f819c03f0

def z223 : W := mkw 0x1289fe21f800b014 0x0944ff10fc00580a 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z224 : W := mkw 0x800000012c0000ab 0x4000000096000055 0x00000000fc00001e 0x000000007e00000f

def z225 : W := mkw 0x1288f420d0000000 0x09447a1068000000 0x0000e00000000000 0x0000700000000000

def z226 : W := mkw 0x017620fec3ac2754 0x00bb107f61d613aa 0xdfff00ffe3fe07ff 0xefff807ff1ff03ff

def z227 : W := mkw 0x0408642090106010 0x8204321048083008 0x0000e0000000e000 0x0000700000007000

def z228 : W := mkw 0x000c647491002410 0x0006323a48801208 0xf81ce7f49f01e419 0x7c0e73fa4f80f20c

def z229 : W := mkw 0x044420fcd508279d 0x8222107e6a8413ce 0x100000fcfc00079e 0x0800007e7e0003cf

def z230 : W := mkw 0x00c1baa9e8000000 0x0060dd54f4000000 0xf3e3fffffc000001 0xf9f1fffffe000000

def z231 : W := mkw 0x0004005401080500 0x0002002a00840280 0x100000f400000580 0x0800007a000002c0

def z232 : W := mkw 0x931f4f473c4308ab 0x498fa7a39e218455 0x041f07071c4601e1 0x020f83838e2300f0

def z233 : W := mkw 0x0132000002a40000 0x0099000001520000 0xcfff000003fe0001 0xe7ff800001ff0000

def z234 : W := mkw 0x004400de01080740 0x0022006f008403a0 0x000000f000000000 0x0000007800000000

def z235 : W := mkw 0x0172008a02a40240 0x00b9004501520120 0x5fe3000f00c607e1 0xaff18007806303f0

def z236 : W := mkw 0x8bfbffb9eff7febf 0x45fdffdcf7fbff5f 0xffffffffffffffff 0xffffffffffffffff

def z237 : W := mkw 0x01f690de03ac9740 0x00fb486f01d64ba0 0xfffff8ff03ffffe1 0xfffffc7f81fffff0

def z238 : W := mkw 0x040c454414594189 0x820622a20a2ca0c4 0x7c1c07049c790599 0x3e0e03824e3c82cc

def z239 : W := mkw 0x0fbef47493bcf510 0x87df7a3a49de7a88 0x83fce0f00338e000 0x41fe7078019c7000

def z240 : W := mkw 0x17dffefffd082599 0x8befff7ffe8412cc 0xf3fffffffc000599 0xf9fffffffe0002cc

def z241 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xa3fcff000339f800 0x51fe7f80019cfc00

def z242 : W := mkw 0x000000000000b014 0x000000000000580a 0x000000000001f81e 0x000000000000fc0f

def z243 : W := mkw 0x000d6e65b8000000 0x0006b732dc000000 0xf01ffffffc000001 0xf80ffffffe000000

def z244 : W := mkw 0x03fbfeb8c380b614 0x01fdff5c61c05b0a 0xfbfffff8e381fe1f 0xfdfffffc71c0ff0f

def z245 : W := mkw 0x88210b012ef7d8ab 0x44108580977bec55 0x7c031f0fffffffff 0xbe018f87ffffffff

def z246 : W := mkw 0x800000012c0000ab 0x4000000096000055 0x1000000ffc0007fe 0x08000007fe0003ff

def z247 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff0f03ffffe1 0xffffff8781fffff0

def z248 : W := mkw 0x0820011003f7fe14 0x0410008801fbff0a 0x0c00000003fffe1e 0x0600000001ffff0f

def z249 : W := mkw 0x0060009803ac0740 0x0030004c01d603a0 0xdfe000f803fe07e0 0xeff0007c01ff03f0

def z250 : W := mkw 0x00a19b0002c39800 0x0050cd800161cc00 0xefe3ff0003c7f801 0xf7f1ff8001e3fc00

def z251 : W := mkw 0x800d6f65bc4308ab 0x4006b7b2de218455 0xfc1ffffffcc71fff 0xfe0ffffffe638fff

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x5800000800800600 0xac00000400400300

def z253 : W := mkw 0x0b3b4f0002f7d800 0x059da780017bec00 0x0c1f070003fff801 0x060f838001fffc00

def z254 : W := mkw 0x0b9bdf000053d800 0x05cdef800029ec00 0xe3ffff000001f801 0xf1ffff800000fc00

def z255 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x87ffe700037ee001 0x43fff38001bf7000

def z256 : W := mkw 0x80210b112fef0feb 0x4010858897f787f5 0x7c031f0fffff1fff 0xbe018f87ffff8fff

def z257 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x000007001c000000 0x000003800e000000

def z258 : W := mkw 0x81170b472c6f09eb 0x408b85a3963784f5 0x7c1f1f0ffcff1fff 0xbe0f8f87fe7f8fff

def z259 : W := mkw 0x01160046002c0140 0x008b0023001600a0 0x001c000000380000 0x000e0000001c0000

def z260 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xffff18ffe3ff1fff 0xffff8c7ff1ff8fff

def z261 : W := mkw 0x13fffefffb80b614 0x09ffff7ffdc05b0a 0xf3ffffffff00e001 0xf9ffffffff807000

def z262 : W := mkw 0x13dbde8b68000000 0x09edef45b4000000 0xe3ffff0b60000001 0xf1ffff85b0000000

def z263 : W := mkw 0x0bbfff6492f7d800 0x05dfffb2497bec00 0xfffffff49ffff801 0xfffffffa4ffffc00

def z264 : W := mkw 0x0000203081002410 0x0000101840801208 0x100000f080000418 0x080000784000020c

def z265 : W := mkw 0x00e4b0fcc388b714 0x0072587e61c45b8a 0xfffcf8fce3f9ff9f 0xfffe7c7e71fcffcf

def z266 : W := mkw 0x000c656490514000 0x000632b24828a000 0xfc1ce7f49f79e001 0x7e0e73fa4fbcf000

def z267 : W := mkw 0x0ae9ffb8c3d3fe14 0x0574ffdc61e9ff0a 0xfbe0fff8e381fe1e 0xfdf07ffc71c0ff0f

def z268 : W := mkw 0x0080b030c100b414 0x0040581860805a0a 0xf800f8f0e301fc1e 0x7c007c787180fe0f

def z269 : W := mkw 0x040c656494596199 0x820632b24a2cb0cc 0x241ce7049c79e199 0x120e73824e3cf0cc

def z270 : W := mkw 0x0b3b4f0002f74800 0x059da780017ba400 0xcfff070003fe0001 0xe7ff838001ff0000

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003000b00860260 0x8001800580430130

def z272 : W := mkw 0x00e0b0b8c3acb754 0x0070585c61d65baa 0xffe0f8f8e3fffffe 0xfff07c7c71ffffff

def z273 : W := mkw 0x042c657497d9f79d 0x821632ba4becfbce 0xfc1ce7f49ff9ff9f 0x7e0e73fa4ffcffcf

def z274 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xebe0f8f00381f800 0xf5f07c7801c0fc00

def z275 : W := mkw 0x80000000040000ab 0x4000000002000055 0x00000000000007fe 0x00000000000003ff

def z276 : W := mkw 0x0420011007d9f79d 0x8210008803ecfbce 0x0c00000003f9ff9e 0x0600000001fcffcf

def z277 : W := mkw 0x131f4e4738000000 0x098fa7239c000000 0x701f1f0ffc000001 0xb80f8f87fe000000

def z278 : W := mkw 0x0bbad50002f5d000 0x05dd6a80017ae800 0xeffce7000379e001 0x77fe738001bcf000

def z279 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z280 : W := mkw 0x131f6e67b8000000 0x098fb733dc000000 0xf01fe7f79c000001 0x780ff3fbce000000

def z281 : W := mkw 0x044420fe950827d9 0x8222107f4a8413ec 0x100000ff9c0007f8 0x0800007fce0003fc

def z282 : W := mkw 0x0820000002b4d000 0x04100000015a6800 0x000000000338e000 0x00000000019c7000

def z283 : W := mkw 0x0bf39a8842a69a04 0x05f9cd4421534d02 0x03e3180860861a06 0x81f18c0430430d03

def z284 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x20031f0bfc871a7e 0x90018f85fe438d3f

def z285 : W := mkw 0x0b1f4f46007f4940 0x058fa7a3003fa4a0 0x041f0707007e01e1 0x020f8383803f00f0

def z286 : W := mkw 0x0400202094002099 0x820010104a00104c 0x000000009c000018 0x000000004e00000c

def z287 : W := mkw 0x80010a012c0208ab 0x4000850096010455 0x1003180ffc861ffe 0x88018c07fe430fff

def z288 : W := mkw 0x00010b012c410089 0x0000858096208044 0x7c031f0ffc410599 0xbe018f87fe2082cc

def z289 : W := mkw 0x0000010000430800 0x0000008000218400 0x0c00000000c71800 0x0600000000638c00

def z290 : W := mkw 0x10452aeff8000000 0x08229577fc000000 0x70031ffffc000001 0xb8018ffffe000000

def z291 : W := mkw 0x0080900000009000 0x0040480000004800 0x2000f8000001f800 0x10007c000000fc00

def z292 : W := mkw 0x0bb39a0002a69800 0x05d9cd0001534c00 0xebe3f8000387f800 0xf5f1fc0001c3fc00

def z293 : W := mkw 0x01f6b0fec3ac0740 0x00fb587f61d603a0 0xfffff8ffe3fe07e1 0xfffffc7ff1ff03f0

def z294 : W := mkw 0x0bffdfde03ffdf40 0x05ffefef01ffefa0 0xeffffff003fff801 0xf7fffff801fffc00

def z295 : W := mkw 0x015600de01080740 0x00ab006f008403a0 0xd3ff00ff000007e1 0xe9ff807f800003f0

def z296 : W := mkw 0x039bdf0000514000 0x01cdef800028a000 0xefffff000379e001 0xf7ffff8001bcf000

def z297 : W := mkw 0x9bffffeffef7d8ab 0x4dfffff7ff7bec55 0xffffffffffffffff 0xffffffffffffffff

def z298 : W := mkw 0x006400dc03880700 0x0032006e01c40380 0xdffc00fc03f80781 0xeffe007e01fc03c0

def z299 : W := mkw 0x00010b0000430800 0x0000858000218400 0x0403070000460001 0x0201838000230000

def z300 : W := mkw 0x0004004400000000 0x0002002200000000 0xd01c00f400000001 0x680e007a00000000

def z301 : W := mkw 0x053e657497fd6599 0x829f32ba4bfeb2cc 0xffffe7f49fffe599 0xfffff3fa4ffff2cc

def z302 : W := mkw 0x040c455415594589 0x820622aa0aaca2c4 0xdc1c07f41f780581 0x6e0e03fa0fbc02c0

def z303 : W := mkw 0x93ffffffffc3bebf 0x49ffffffffe1df5f 0xffffffffffc7ffff 0xffffffffffe3ffff

def z304 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xd3ff00ff03380001 0xe9ff807f819c0000

def z305 : W := mkw 0x804020b9ed0026bf 0x4020105cf680135f 0x100000fffc0007fe 0x0800007ffe0003ff

def z306 : W := mkw 0x040c656494516099 0x820632b24a28b04c 0xf01ce7f49c01e019 0x780e73fa4e00f00c

def z307 : W := mkw 0x00c0b0b8c1002410 0x0060585c60801208 0xfbe0f8f8e301e418 0xfdf07c7c7180f20c

def z308 : W := mkw 0x80010a0128020822 0x4000850094010411 0x0000180060001806 0x00000c0030000c03

def z309 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xa3fcfff0fc000000 0x51fe7ff87e000000

def z310 : W := mkw 0x057e64fe93bc6750 0x82bf327f49de33a8 0x83fce0f00338e000 0x41fe7078019c7000

def z311 : W := mkw 0x0289de0000000000 0x0144ef0000000000 0x2000ff0000000000 0x10007f8000000000

def z312 : W := mkw 0x0bbbde0002b4d000 0x05ddef00015a6800 0xe3ffff000338e001 0xf1ffff80019c7000

def z313 : W := mkw 0x0a819a0000029800 0x0540cd0000014c00 0x0000180000001800 0x00000c0000000c00

def z314 : W := mkw 0x015600de012c0740 0x00ab006f009603a0 0x141f00ff007e07e1 0x0a0f807f803f03f0

def z315 : W := mkw 0x097601de03ffdf40 0x04bb00ef01ffefa0 0xdfff00ff03ffffe1 0xefff807f81fffff0

def z316 : W := mkw 0x0bbbdf012af7d800 0x05ddef80957bec00 0xffffff0ffffff801 0xffffff87fffffc00

def z317 : W := mkw 0x0bfbdf9803f7de00 0x05fdefcc01fbef00 0xfffffff803fffe01 0xfffffffc01ffff00

def z318 : W := mkw 0x0136004602ac0140 0x009b0023015600a0 0xcfff000703fe01e1 0xe7ff800381ff00f0

def z319 : W := mkw 0x004020b8c1002614 0x0020105c6080130a 0x000000f000000000 0x0000007800000000

def z320 : W := mkw 0x0008440000104000 0x0004220000082000 0x801ce0000338e000 0x400e7000019c7000

def z321 : W := mkw 0x8bbbdf0006f7d8ab 0x45ddef80037bec55 0xefffff0003ffffff 0xf7ffff8001ffffff

def z322 : W := mkw 0x0000010004410089 0x0000008002208044 0x040007041c400181 0x020003820e2000c0

def z323 : W := mkw 0x840d4f453c5b49ab 0xc206a7a29e2da4d5 0x7c1f1f0ffcff1fff 0xbe0f8f87fe7f8fff

def z324 : W := mkw 0x80000100044308ab 0x4000008002218455 0x7c001808e0c71ffe 0xbe000c0470638fff

def z325 : W := mkw 0x039bde0128000000 0x01cdef0094000000 0xf3ffff0ffc000001 0xf9ffff87fe000000

def z326 : W := mkw 0x046c65fc97d96799 0x823632fe4becb3cc 0xfffce7fc9ff9e799 0xfffe73fe4ffcf3cc

def z327 : W := mkw 0x0000000000000000 0x0000000000000000 0x4c03000000c60001 0xa601800000630000

def z328 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x83fff8fb60000000 0xc1fffc7db0000000

def z329 : W := mkw 0x00a0900002809000 0x0050480001404800 0xfbe0f808e381fe1e 0xfdf07c0471c0ff0f

def z330 : W := mkw 0x80e0b0b9ef80b6bf 0x4070585cf7c05b5f 0xfbe0f8ffff81fffe 0xfdf07c7fffc0ffff

def z331 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x23e3ff000087f800 0x91f1ff800043fc00

def z332 : W := mkw 0x040c647491186510 0x8206323a488c3288 0xf01ce7f49f38e001 0x780e73fa4f9c7000

def z333 : W := mkw 0x1004004738000000 0x080200239c000000 0x000000071c000000 0x000000038e000000

def z334 : W := mkw 0x0a88d4000010d000 0x05446a0000086800 0x0000e0000000e000 0x0000700000007000

def z335 : W := mkw 0x13d3baabe8000000 0x09e9dd55f4000000 0xf3e3f8fbe0000000 0xf9f1fc7df0000000

def z336 : W := mkw 0x0bfbdf8a02f7da40 0x05fdefc5017bed20 0xefffff0b03fffa61 0xf7ffff8581fffd30

def z337 : W := mkw 0x0aa9df0002f7d800 0x0554ef80017bec00 0x2c00ff0003fff800 0x16007f8001fffc00

def z338 : W := mkw 0x057620fe97ac27d9 0x82bb107f4bd613ec 0xdfff00ff9ffe07f9 0xefff807fcfff03fc

def z339 : W := mkw 0x17def4fed1186510 0x8bef7a7f688c3288 0x83fce0f00338e000 0x41fe7078019c7000

def z340 : W := mkw 0x1bf39a8b6aa69800 0x0df9cd45b5534c00 0x03e3180b60861800 0x81f18c05b0430c00

def z341 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x04031f0f7cc61be7 0x82018f87be630df3

def z342 : W := mkw 0x0020000002809204 0x0010000001404902 0x0000000000801a06 0x0000000000400d03

def z343 : W := mkw 0x0820011003ffdf40 0x0410008801ffefa0 0x0c00000003ffffe0 0x0600000001fffff0

def z344 : W := mkw 0x84052b75bd4b2dbb 0xc20295badea596dd 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z345 : W := mkw 0x057e65fe97fd67d9 0x82bf32ff4bfeb3ec 0xfffce7f49f79e599 0x7ffe73fa4fbcf2cc

def z346 : W := mkw 0x80000100044308ab 0x4000008002218455 0x7c0007049cc71fff 0x3e0003824e638fff

def z347 : W := mkw 0x13fffeeffa809000 0x09ffff77fd404800 0xfbffffffff81f801 0xfdffffffffc0fc00

def z348 : W := mkw 0x93dfffeffc4308ab 0x49effff7fe218455 0xf7fffffffc4601e1 0xfbfffffffe2300f0

def z349 : W := mkw 0x0bfed4de03bcd740 0x05ff6a6f01de6ba0 0xdfffe0ff03fee7e1 0xeffff07f81ff73f0

def z350 : W := mkw 0x81770bdf2fef0feb 0x40bb85ef97f787f5 0xdfff07ff1ffe07e1 0xefff83ff8fff03f0

def z351 : W := mkw 0x013a450002f54000 0x009d2280017aa000 0xefffe70003ffe001 0xf7fff38001fff000

def z352 : W := mkw 0x80e19b896ec39aaf 0x4070cdc4b761cd57 0x7fe31f0ffcc71fff 0xbff18f87fe638fff

def z353 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x20001f00fc01181e 0x10000f807e008c0f

def z354 : W := mkw 0x139ffe67f8000000 0x09cfff33fc000000 0x201fff07fc000001 0x100fff83fe000000

def z355 : W := mkw 0x80450bdf2d4b0feb 0x402285ef96a587f5 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z356 : W := mkw 0x1a89ff21f853d800 0x0d44ff90fc29ec00 0x2000ff00fc01f800 0x10007f807e00fc00

def z357 : W := mkw 0x800000012c0000ab 0x4000000096000055 0x5c03000ffcc607ff 0xae018007fe6303ff

def z358 : W := mkw 0x01d6b0eec0000000 0x00eb587760000000 0xf3fff8ffe0000001 0xf9fffc7ff0000000

def z359 : W := mkw 0x80000100044308ab 0x4000008002218455 0x04000000004601e0 0x02000000002300f0

def z360 : W := mkw 0x80050b552d4b0dab 0x400285aa96a586d5 0xfc1f1fffffff1fff 0xfe0f8fffffff8fff

def z361 : W := mkw 0x93d39a8b68020822 0x49e9cd45b4010411 0x03e3180b60861a66 0x81f18c05b0430d33

def z362 : W := mkw 0x0004206490000000 0x0002103248000000 0x100000f49c000000 0x0800007a4e000000

def z363 : W := mkw 0x81730a8b2aa60a62 0x40b9854595530531 0x03e3180b60861a66 0x81f18c05b0430d33

def z364 : W := mkw 0x044c65fcd559679d 0x822632fe6aacb3ce 0xfc1ce7fcff79e79f 0x7e0e73fe7fbcf3cf

def z365 : W := mkw 0x006400de03ac0740 0x0032006f01d603a0 0x1c0000ff03fe07e0 0x0e00007f81ff03f0

def z366 : W := mkw 0x0bb39a0002a69800 0x05d9cd0001534c00 0xcfff180003fe1801 0xe7ff8c0001ff0c00

def z367 : W := mkw 0x1bfffffffbffdf40 0x0dfffffffdffefa0 0xffffffffffffffe1 0xfffffffffffffff0

def z368 : W := mkw 0x015600de01080500 0x00ab006f00840280 0xdfff00ff03780581 0xefff807f81bc02c0

def z369 : W := mkw 0x93dffeeffc0000ab 0x49efff77fe000055 0xf3fffffffc0007ff 0xf9fffffffe0003ff

def z370 : W := mkw 0x0ffffffcd7ffff9d 0x87fffffe6bffffce 0xfffffffcffffff9f 0xfffffffe7fffffcf

def z371 : W := mkw 0x00094f0000534800 0x0004a7800029a400 0xec1fff0003fff801 0xf60fff8001fffc00

def z372 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000008e000061e 0x080000047000030f

def z373 : W := mkw 0x840c6575bd5965bb 0xc20632badeacb2dd 0xfc1ce7ffff79e7ff 0x7e0e73ffffbcf3ff

def z374 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x6c031f071cc719e1 0xb6018f838e638cf0

def z375 : W := mkw 0x040c656494594189 0x820632b24a2ca0c4 0xf41ce7f49c780181 0x7a0e73fa4e3c00c0

def z376 : W := mkw 0x1bbfdf473af7d800 0x0ddfefa39d7bec00 0xefffff071ffff801 0xf7ffff838ffffc00

def z377 : W := mkw 0x04e8f5b8d7d1f69d 0x82747adc6be8fb4e 0xfbe0fff8ff81fe1e 0xfdf07ffc7fc0ff0f

def z378 : W := mkw 0x0060008802800200 0x0030004401400100 0x03e0000800800200 0x81f0000400400100

def z379 : W := mkw 0x01f2908a42a49244 0x00f9484521524922 0x03e3180b60861a66 0x81f18c05b0430d33

def z380 : W := mkw 0x01f6b0fec3acb754 0x00fb587f61d65baa 0xdfffe0ff03fee7e1 0xeffff07f81ff73f0

def z381 : W := mkw 0x0000010004410089 0x0000008002208044 0x7c03070f9cc707f9 0xbe018387ce6383fc

def z382 : W := mkw 0x01770bde03ef0f40 0x00bb85ef01f787a0 0xffff1fff03ff1fe1 0xffff8fff81ff8ff0

def z383 : W := mkw 0x0fbef57497fdf599 0x87df7aba4bfefacc 0xfffce7f49f79e599 0x7ffe73fa4fbcf2cc

def z384 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x8ffc00f003fe07e0 0x47fe007801ff03f0

def z385 : W := mkw 0x00e0908842809204 0x0070484421404902 0xebe0f8086381fa06 0xf5f07c0431c0fd03

def z386 : W := mkw 0x13dfffeff8430800 0x09effff7fc218400 0xfffffffffcc71801 0xfffffffffe638c00

def z387 : W := mkw 0x006400de03880740 0x0032006f01c403a0 0xdbe000ff038007e0 0xedf0007f81c003f0

def z388 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x5c03070f1cc607e1 0xae0183878e6303f0

def z389 : W := mkw 0x1bdfffeff8774800 0x0deffff7fc3ba400 0xf7fffffffc7e0001 0xfbfffffffe3f0000

def z390 : W := mkw 0x079fff7495596599 0x83cfffba4aacb2cc 0xfffffff49f79e599 0xfffffffa4fbcf2cc

def z391 : W := mkw 0x139fde4738000000 0x09cfef239c000000 0xe3ffff071c000001 0xf1ffff838e000000

def z392 : W := mkw 0x80c1bba9ec4308ab 0x4060ddd4f6218455 0xffe3fffffcc71fff 0xfff1fffffe638fff

def z393 : W := mkw 0x00010a0128000000 0x0000850094000000 0x7c031f0ffcc607e1 0xbe018f87fe6303f0

def z394 : W := mkw 0x0820000002a69800 0x0410000001534c00 0x0000000000861800 0x0000000000430c00

def z395 : W := mkw 0x0bb39b0002e79800 0x05d9cd800173cc00 0x6fe31f0000c71801 0xb7f18f8000638c00

def z396 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x78001f08fc811e1e 0xbc000f847e408f0f

def z397 : W := mkw 0x051e4546147d41c9 0x828f22a30a3ea0e4 0x041f07071c7e01e1 0x020f83838e3f00f0

def z398 : W := mkw 0x13dfffeffc410089 0x09effff7fe208044 0xfffffffffc410599 0xfffffffffe2082cc

def z399 : W := mkw 0x00e0b0b8c3800600 0x0070585c61c00300 0xfbe0f8f8e3800600 0xfdf07c7c71c00300

def z400 : W := mkw 0x0404015405596599 0x820200aa02acb2cc 0xdc1c00f40379e599 0x6e0e007a01bcf2cc

def z401 : W := mkw 0x0020001003ac0740 0x0010000801d603a0 0x5c03000f03fe07e1 0xae01800781ff03f0

def z402 : W := mkw 0x13130a0328000000 0x0989850194000000 0x0003000300000000 0x0001800180000000

def z403 : W := mkw 0x817600df2fac07eb 0x40bb006f97d603f5 0xdfff00fffffe07ff 0xefff807fffff03ff

def z404 : W := mkw 0x0060009803800600 0x0030004c01c00300 0xdfe300ff03c607e1 0xeff1807f81e303f0

def z405 : W := mkw 0x0408652094516099 0x820432904a28b04c 0xec1ce7009f79e019 0x760e73804fbcf00c

def z406 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff00fffff81f 0xf7ffff807ffffc0f

def z407 : W := mkw 0x01b2900002a49000 0x00d9480001524800 0xeffff80003fff801 0xf7fffc0001fffc00

def z408 : W := mkw 0x1289fe21f8000000 0x0944ff10fc000000 0x7003ff0ffc000001 0xb801ff87fe000000

def z409 : W := mkw 0x1ffffffffffffd99 0x8ffffffffffffecc 0xfffffffffffffd99 0xfffffffffffffecc

def z410 : W := mkw 0x040c647491186510 0x8206323a488c3288 0xf81ce0f08339e418 0x7c0e7078419cf20c

def z411 : W := mkw 0x8bffdfdf2fffdfeb 0x45ffefef97ffeff5 0xffffffffffffffff 0xffffffffffffffff

def z412 : W := mkw 0x97dffffffd5b6dbb 0xcbeffffffeadb6dd 0xffffffffffffffff 0xffffffffffffffff

def z413 : W := mkw 0x13f3babbeb80b614 0x09f9dd5df5c05b0a 0xfbe3f8fbe381fe1e 0xfdf1fc7df1c0ff0f

def z414 : W := mkw 0x0bbfdf5403ffdd00 0x05dfefaa01ffee80 0xfffffff403fffd81 0xfffffffa01fffec0

def z415 : W := mkw 0x904420effc0000ab 0x48221077fe000055 0x100000fffc0007fe 0x0800007ffe0003ff

def z416 : W := mkw 0x0aa9df0002d3d800 0x0554ef800169ec00 0xebe0ff000381f800 0xf5f07f8001c0fc00

def z417 : W := mkw 0x015600ce002c0140 0x00ab0067001600a0 0xd7ff00ff007e01e1 0xebff807f803f00f0

def z418 : W := mkw 0x857f6fffbfff6ffb 0xc2bfb7ffdfffb7fd 0xffffffffffffffff 0xffffffffffffffff

def z419 : W := mkw 0x80010a0128020822 0x4000850094010411 0x0003000300060060 0x0001800180030030

def z420 : W := mkw 0x8a89df012c53d8ab 0x4544ef809629ec55 0x7c03ff0ffcc7ffff 0xbe01ff87fe63ffff

def z421 : W := mkw 0x01160056012c0540 0x008b002b009602a0 0xdc1f00f7037e05e1 0x6e0f807b81bf02f0

def z422 : W := mkw 0x00010b0000430800 0x0000858000218400 0x7c031f08e0c71e1f 0xbe018f8470638f0f

def z423 : W := mkw 0x80210b112fc3bebf 0x4010858897e1df5f 0x7c031f0fffc7ffff 0xbe018f87ffe3ffff

def z424 : W := mkw 0x042c657497fd67d9 0x821632ba4bfeb3ec 0xfc1ce7f49fffe7f9 0x7e0e73fa4ffff3fc

def z425 : W := mkw 0x12e9feb9fb80b614 0x0974ff5cfdc05b0a 0xfbe0fff8ff81fe1e 0xfdf07ffc7fc0ff0f

def z426 : W := mkw 0x13fef4fed3ac0740 0x09ff7a7f69d603a0 0x83fce0f003380000 0x41fe7078019c0000

def z427 : W := mkw 0x13d7baeff8000000 0x09ebdd77fc000000 0x13e318fffc000000 0x89f18c7ffe000000

def z428 : W := mkw 0x1689ff21fc516099 0x8b44ff90fe28b04c 0x2000ff00fc01e018 0x10007f807e00f00c

def z429 : W := mkw 0x0040008840000204 0x0020004420000102 0x0000000860000206 0x0000000430000103

def z430 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x83e0f8f86380fa06 0xc1f07c7c31c07d03

def z431 : W := mkw 0x0bbfdf4602ffd940 0x05dfefa3017feca0 0xefffff0703fff9e1 0xf7ffff8381fffcf0

def z432 : W := mkw 0x8081bb21ec43b8bf 0x4040dd90f621dc5f 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z433 : W := mkw 0x84096f21bc5368bb 0xc204b790de29b45d 0x7c03ff0ffcc7ffff 0xbe01ff87fe63ffff

def z434 : W := mkw 0x0c2c657497fffd99 0x861632ba4bfffecc 0xfc1ce7f49ffffd99 0x7e0e73fa4ffffecc

def z435 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x0c03180b60c71ffe 0x86018c05b0638fff

def z436 : W := mkw 0x10c4b0eff8000000 0x08625877fc000000 0xf3e0f8fffc000000 0xf9f07c7ffe000000

def z437 : W := mkw 0x8020011007c3bebf 0x4010008803e1df5f 0x0c00000003c7fffe 0x0600000001e3ffff

def z438 : W := mkw 0x80010b0128430822 0x4000858094218411 0x6c031f0b60c71a67 0xb6018f85b0638d33

def z439 : W := mkw 0x80010a0128020822 0x4000850094010411 0x5c03180f60c61fe7 0xae018c07b0630ff3

def z440 : W := mkw 0x0172009803a40600 0x00b9004c01d20300 0xdfff00f803fe0601 0xefff807c01ff0300

def z441 : W := mkw 0x17fffffffffd67d9 0x8bfffffffffeb3ec 0xffffffffffffe7f9 0xfffffffffffff3fc

def z442 : W := mkw 0x004020b8c1002614 0x0020105c6080130a 0x780018f8e0811e1e 0xbc000c7c70408f0f

def z443 : W := mkw 0x17ffffffffd9f79d 0x8bffffffffecfbce 0xfffffffffff9ff9f 0xfffffffffffcffcf

def z444 : W := mkw 0x0000010004410089 0x0000008002208044 0x7c001f0cfcc11f9f 0xbe000f867e608fcf

def z445 : W := mkw 0x015600ce00000000 0x00ab006700000000 0x83fc00f000000000 0x41fe007800000000

def z446 : W := mkw 0x80000100044308ab 0x4000008002218455 0x000000000001181e 0x0000000000008c0f

def z447 : W := mkw 0x00e1bbb8c3c3be14 0x0070dddc61e1df0a 0xffe3fff8e3c7fe1f 0xfff1fffc71e3ff0f

def z448 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x24031f07fc4719ff 0x12018f83fe238cff

def z449 : W := mkw 0x80094f012c5348ab 0x4004a7809629a455 0xfc1fff0fffffffff 0xfe0fff87ffffffff

def z450 : W := mkw 0x117620fffbac0740 0x08bb107ffdd603a0 0xdfff00fffffe07e1 0xefff807fffff03f0

def z451 : W := mkw 0x0004004400080100 0x0002002200040080 0x041c000400780181 0x020e0002003c00c0

def z452 : W := mkw 0x0c20011007fffd99 0x8610008803fffecc 0x0c00000003fffd98 0x0600000001fffecc

def z453 : W := mkw 0x0116004600000000 0x008b002300000000 0x001f000700000001 0x000f800380000000

def z454 : W := mkw 0x17dfffeffc594189 0x8beffff7fe2ca0c4 0xf7fffffffc780181 0xfbfffffffe3c00c0

def z455 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x0c0307071cc71fff 0x060183838e638fff

def z456 : W := mkw 0x01160046002c0140 0x008b0023001600a0 0x5c1f000f00fe07e1 0xae0f8007807f03f0

def z457 : W := mkw 0x0fbbff2096f7f899 0x87ddff904b7bfc4c 0xefffff009ffff819 0xf7ffff804ffffc0c

def z458 : W := mkw 0x01f6b0fec3acb754 0x00fb587f61d65baa 0xfbfcf8f8e3b9fe1e 0xfdfe7c7c71dcff0f

def z459 : W := mkw 0x931f4f473c4308ab 0x498fa7a39e218455 0x7c1f1f0ffcc71fff 0xbe0f8f87fe638fff

def z460 : W := mkw 0x131f4e47382c0140 0x098fa7239c1600a0 0x041f07071c7e01e1 0x020f83838e3f00f0

def z461 : W := mkw 0x00010a0000020800 0x0000850000010400 0x0003180000861800 0x80018c0000430c00

def z462 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xcfff00f003fe0001 0xe7ff807801ff0000

def z463 : W := mkw 0x800000012c0000ab 0x4000000096000055 0x000000071c0001e0 0x000000038e0000f0

def z464 : W := mkw 0x0004005401080500 0x0002002a00840280 0x801c00f003380000 0x400e0078019c0000

def z465 : W := mkw 0x00a0b020c280b014 0x005058106140580a 0xebe0f800e381f81e 0xf5f07c0071c0fc0f

def z466 : W := mkw 0x80010a0128020822 0x4000850094010411 0x70031f0ffc861a67 0xb8018f87fe430d33

def z467 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x1403070ffc4607ff 0x0a018387fe2303ff

def z468 : W := mkw 0x00e0909843809604 0x0070484c21c04b02 0xdbe018f863801e06 0xedf00c7c31c00f03

def z469 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x93e0e0f8e300e61e 0x49f0707c7180730f

def z470 : W := mkw 0x9289ff21fc4308ab 0x4944ff90fe218455 0x2000ff00fc01181e 0x10007f807e008c0f

def z471 : W := mkw 0x80012b31ad432cbb 0x40009598d6a1965d 0xfc03ffffffc7ffff 0xfe01ffffffe3ffff

def z472 : W := mkw 0x0000000128000000 0x0000000094000000 0x1000000ffc000000 0x08000007fe000000

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0xe800e0000301e000 0x740070000180f000

def z474 : W := mkw 0x0400001001186510 0x82000008008c3288 0x000000000338e000 0x00000000019c7000

def z475 : W := mkw 0x80010a012c0000ab 0x4000850096000055 0x70031f0ffc0007ff 0xb8018f87fe0003ff

def z476 : W := mkw 0x0b1b4f0000774800 0x058da780003ba400 0x6c1f1f0000ff1801 0xb60f8f80007f8c00

def z477 : W := mkw 0x0800010000774800 0x04000080003ba400 0x04000000007e0000 0x02000000003f0000

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x700007049c000001 0x380003824e000000

def z479 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe0e0f08301e418 0x7df070784180f20c

def z480 : W := mkw 0x00e0b0a8c2809204 0x0070585461404902 0xf3e0f8f8e0801a06 0xf9f07c7c70400d03

def z481 : W := mkw 0x0172009a03ac0740 0x00b9004d01d603a0 0x0fe3000b03fe07e0 0x87f1800581ff03f0

def z482 : W := mkw 0x13f39a8b6aa40240 0x09f9cd45b5520120 0x03e3180b60860260 0x81f18c05b0430130

def z483 : W := mkw 0x13f39a8b6a809204 0x09f9cd45b5404902 0x03e3180b60801a06 0x81f18c05b0400d03

def z484 : W := mkw 0x00e1bab9eb80b614 0x0070dd5cf5c05b0a 0xfbe3ffffff81fe1f 0xfdf1ffffffc0ff0f

def z485 : W := mkw 0x817601de07ef0feb 0x40bb00ef03f787f5 0xdfff00ff03ff1fff 0xefff807f81ff8fff

def z486 : W := mkw 0x0020001003ac0740 0x0010000801d603a0 0x0000000003380000 0x00000000019c0000

def z487 : W := mkw 0x13fffefffbacb754 0x09ffff7ffdd65baa 0xffffffffffffffff 0xffffffffffffffff

def z488 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x7c0307079c4705f9 0x3e018383ce2382fc

def z489 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdbfc00f803b80600 0xedfe007c01dc0300

def z490 : W := mkw 0x017e45de03fd4740 0x00bf22ef01fea3a0 0xffffe7ff03ffe7e1 0xfffff3ff81fff3f0

def z491 : W := mkw 0x03ffdede03ac0740 0x01ffef6f01d603a0 0xffffffff03fe07e1 0xffffffff81ff03f0

def z492 : W := mkw 0x0020000002809000 0x0010000001404800 0x080000000381f800 0x0400000001c0fc00

def z493 : W := mkw 0x031b4e0000000000 0x018da70000000000 0x001f070000000001 0x000f838000000000

def z494 : W := mkw 0x01f690de43ac9744 0x00fb486f21d64ba2 0xdfff18ff63fe1fe7 0xefff8c7fb1ff0ff3

def z495 : W := mkw 0x040c444410184100 0x82062222080c2080 0x001c000000380000 0x000e0000001c0000

def z496 : W := mkw 0x144c65fffd596599 0x8a2632fffeacb2cc 0xfc1ce7ffff79e599 0x7e0e73ffffbcf2cc

def z497 : W := mkw 0x00002020c0002014 0x000010106000100a 0x00000000e000001e 0x000000007000000f

def z498 : W := mkw 0x0f1f6f74957f6d99 0x878fb7ba4abfb6cc 0xfc1fe7f49f7fe599 0x7e0ff3fa4fbff2cc

def z499 : W := mkw 0x0bfed4de03bcd740 0x05ff6a6f01de6ba0 0x83fce0f00338e000 0x41fe7078019c7000

def z500 : W := mkw 0x8bb39a012aa69822 0x45d9cd0095534c11 0x03e3180b60861a66 0x81f18c05b0430d33

def z501 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdffc00f403780581 0x6ffe007a01bc02c0

def z502 : W := mkw 0x0000203081002410 0x0000101840801208 0x8000e0f00300e000 0x4000707801807000

def z503 : W := mkw 0x002000100380b614 0x0010000801c05b0a 0x000000000300e000 0x0000000001807000

def z504 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xdbe0e0f80380e600 0xedf0707c01c07300

def z505 : W := mkw 0x0000000004000089 0x0000000002000044 0x100000049c000598 0x080000024e0002cc

def z506 : W := mkw 0x0bf79ade03ae9f40 0x05fbcd6f01d74fa0 0xdfff18ff03fe1fe1 0xefff8c7f81ff0ff0

def z507 : W := mkw 0x017e64fe93ac0740 0x00bf327f49d603a0 0xffffe7ff9ffe07e1 0xfffff3ffcfff03f0

def z508 : W := mkw 0x057e64fe93bc6750 0x82bf327f49de33a8 0xdfffe0ff03fee7e1 0xeffff07f81ff73f0

def z509 : W := mkw 0x80e0b1b8c7c3bebf 0x407058dc63e1df5f 0xffe0f8f8e3c7fffe 0xfff07c7c71e3ffff

def z510 : W := mkw 0x0b1b4f0000774800 0x058da780003ba400 0xec1fe700037fe001 0x760ff38001bff000

def z511 : W := mkw 0x04acf57497d9f599 0x82567aba4becfacc 0xfffcfff49ff9fd99 0xfffe7ffa4ffcfecc

def z512 : W := mkw 0x01770adf2bac0740 0x00bb856f95d603a0 0xffff1ffffffe07e1 0xffff8fffffff03f0

def z513 : W := mkw 0x0008450000514000 0x000422800028a000 0x041c070000780001 0x020e0380003c0000

def z514 : W := mkw 0x017600de03800600 0x00bb006f01c00300 0xdbff00ff03800601 0xedff807f81c00300

def z515 : W := mkw 0x0408653095596599 0x820432984aacb2cc 0x2c00e7009f79e598 0x160073804fbcf2cc

def z516 : W := mkw 0x8000000128000022 0x4000000094000011 0x0000000b60000266 0x00000005b0000133

def z517 : W := mkw 0x1bfffeeffab4d000 0x0dffff77fd5a6800 0xf3ffffffff38e001 0xf9ffffffff9c7000

def z518 : W := mkw 0x040c647491186510 0x8206323a488c3288 0xdc1ce0f40378e581 0x6e0e707a01bc72c0

def z519 : W := mkw 0x1bfffeeffaa69800 0x0dffff77fd534c00 0xf3fffffffc861801 0xf9fffffffe430c00

def z520 : W := mkw 0x08e0b1b8c3f7fe14 0x047058dc61fbff0a 0xffe0f8f8e3fffe1e 0xfff07c7c71ffff0f

def z521 : W := mkw 0x04ecf4fcd398f714 0x82767a7e69cc7b8a 0xfbfcf8f8e3b9fe1e 0xfdfe7c7c71dcff0f

def z522 : W := mkw 0x0080900000000000 0x0040480000000000 0xe3e0f80000000000 0xf1f07c0000000000

def z523 : W := mkw 0x0404207495082599 0x8202103a4a8412cc 0xf800e0f49f01e598 0x7c00707a4f80f2cc

def z524 : W := mkw 0x84010b112d5b6dbb 0xc200858896adb6dd 0x7c031f0fffffffff 0xbe018f87ffffffff

def z525 : W := mkw 0x0136005403ac0500 0x009b002a01d60280 0xdfff00f403fe0581 0xefff807a01ff02c0

def z526 : W := mkw 0x0000000000000000 0x0000000000000000 0x5c00000400400581 0x2e000002002002c0

def z527 : W := mkw 0x0420011007fd67d9 0x8210008803feb3ec 0x0c00000003ffe7f8 0x0600000001fff3fc

def z528 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0xf3fce7f49c000001 0x79fe73fa4e000000

def z529 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1fe7ff9fffe7f9 0xfe0ff3ffcffff3fc

def z530 : W := mkw 0x93dfffeffc4308ab 0x49effff7fe218455 0xf3fffffffc01181f 0xf9fffffffe008c0f

def z531 : W := mkw 0x080001000053d800 0x040000800029ec00 0x000000000001f800 0x000000000000fc00

def z532 : W := mkw 0x0000001001000400 0x0000000800800200 0xd80000f003000400 0x6c00007801800200

def z533 : W := mkw 0x0080b020c0000000 0x0040581060000000 0x2000f800e0000000 0x10007c0070000000

def z534 : W := mkw 0x0152008a00000000 0x00a9004500000000 0x03e3000b00000000 0x81f1800580000000

def z535 : W := mkw 0x80e1bab9eb82be36 0x4070dd5cf5c15f1b 0xfbe3f8fbe387fe7e 0xfdf1fc7df1c3ff3f

def z536 : W := mkw 0x03dbfea8c0000000 0x01edff5460000000 0xf3fffff8e0000001 0xf9fffffc70000000

def z537 : W := mkw 0x1bfffffffbf7fe14 0x0dfffffffdfbff0a 0xfffffffffffffe1f 0xffffffffffffff0f

def z538 : W := mkw 0x0020000002a40000 0x0010000001520000 0x0c00000003fe0000 0x0600000001ff0000

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x04030007004601e1 0x02018003802300f0

def z540 : W := mkw 0x80010a0128020822 0x4000850094010411 0x7803180be0871e7e 0xbc018c05f0438f3f

def z541 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x74031f0ffc4601e1 0xba018f87fe2300f0

def z542 : W := mkw 0x115620eff8000000 0x08ab1077fc000000 0xd3ff00fffc000001 0xe9ff807ffe000000

def z543 : W := mkw 0x13fef4fed3ac0740 0x09ff7a7f69d603a0 0xdfffe0ff03fe07e1 0xeffff07f81ff03f0

def z544 : W := mkw 0x0408653095516499 0x820432984aa8b24c 0xf800e7f09f01e418 0x7c0073f84f80f20c

def z545 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x7c001f04fc411d9f 0x3e000f827e208ecf

def z546 : W := mkw 0x048cf574d559f59d 0x82467aba6aacface 0xfc1cfff4ff79fd9f 0x7e0e7ffa7fbcfecf

def z547 : W := mkw 0x171f6f77bd596599 0x8b8fb7bbdeacb2cc 0xfc1fe7f79f79e599 0x7e0ff3fbcfbcf2cc

def z548 : W := mkw 0x0ffffffe97ffffd9 0x87ffffff4bffffec 0xffffffff9ffffff9 0xffffffffcffffffc

def z549 : W := mkw 0x13fffeeffaa40240 0x09ffff77fd520120 0xf3fffffffc860261 0xf9fffffffe430130

def z550 : W := mkw 0x168dff75fd596599 0x8b46ffbafeacb2cc 0xfc1cfff4ff79e599 0x7e0e7ffa7fbcf2cc

def z551 : W := mkw 0x017601de07ed07c9 0x00bb00ef03f683e4 0xffff07ff9fff07f9 0xffff83ffcfff83fc

def z552 : W := mkw 0x040c657491596510 0x820632ba48acb288 0xec1ce7f00379e001 0x760e73f801bcf000

def z553 : W := mkw 0x03dfdece00000000 0x01efef6700000000 0xf3ffffff00000001 0xf9ffffff80000000

def z554 : W := mkw 0x01330b0002e70800 0x0099858001738400 0xefff1f0003ff1801 0xf7ff8f8001ff8c00

def z555 : W := mkw 0x00a0900002809000 0x0050480001404800 0x03e0180000801800 0x81f00c0000400c00

def z556 : W := mkw 0x13fffeeffa809204 0x09ffff77fd404902 0xf3fffffffc801a07 0xf9fffffffe400d03

def z557 : W := mkw 0x0a89ff20c053f814 0x0544ff906029fc0a 0x2000ff00e001f81e 0x10007f807000fc0f

def z558 : W := mkw 0x0000000000000000 0x0000000000000000 0x70001808e0000000 0xb8000c0470000000

def z559 : W := mkw 0x8fbfff75bffffdbb 0xc7dfffbadffffedd 0xffffffffffffffff 0xffffffffffffffff

def z560 : W := mkw 0x0000202080000000 0x0000101040000000 0xf000e0f080000000 0x7800707840000000

def z561 : W := mkw 0x00010b0004430889 0x0000858002218444 0x7c031f049cc71d99 0xbe018f824e638ecc

def z562 : W := mkw 0x0004015405490589 0x000200aa02a482c4 0xfc1c07f49f790599 0x7e0e03fa4fbc82cc

def z563 : W := mkw 0x80e1bbb9efc3bebf 0x4070dddcf7e1df5f 0xfbe0fff8ff81fe1e 0xfdf07ffc7fc0ff0f

def z564 : W := mkw 0x10e4b0fffb80b614 0x0872587ffdc05b0a 0xfbe0f8ffff81fe1e 0xfdf07c7fffc0ff0f

def z565 : W := mkw 0x0020000002800000 0x0010000001400000 0xcbe0000003800000 0xe5f0000001c00000

def z566 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x07ff1f0000fe1801 0x83ff8f80007f0c00

def z567 : W := mkw 0x040c454414594189 0x820622a20a2ca0c4 0xec1ce7041f79e181 0x760e73820fbcf0c0

def z568 : W := mkw 0x017600ce02a40240 0x00bb006701520120 0xd3ff00ff00860261 0xe9ff807f80430130

def z569 : W := mkw 0x8820010006f7d8ab 0x44100080037bec55 0x0c00000003fffffe 0x0600000001ffffff

def z570 : W := mkw 0x00000000002c0140 0x00000000001600a0 0x04000000007e01e0 0x02000000003f00f0

def z571 : W := mkw 0x80000100044308ab 0x4000008002218455 0x5c03000f00c71fff 0xae01800780638fff

def z572 : W := mkw 0x004400de01080740 0x0022006f008403a0 0xdc1c00ff037807e1 0x6e0e007f81bc03f0

def z573 : W := mkw 0x000c444410000000 0x0006222208000000 0x001c07041c000001 0x000e03820e000000

def z574 : W := mkw 0x131e444610000000 0x098f222308000000 0x001c000000000000 0x000e000000000000

def z575 : W := mkw 0x1bbbff21faf7d800 0x0dddff90fd7bec00 0xefffff00fffff801 0xf7ffff807ffffc00

def z576 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff071ffff9e1 0xf7ffff838ffffcf0

def z577 : W := mkw 0x0404207495082599 0x8202103a4a8412cc 0xdc1c00f49f780599 0x6e0e007a4fbc02cc

def z578 : W := mkw 0x800001012c4308ab 0x4000008096218455 0x1c00000ffcc71ffe 0x0e000007fe638fff

def z579 : W := mkw 0x17def5fed5596599 0x8bef7aff6aacb2cc 0xfffce7f49f79e599 0x7ffe73fa4fbcf2cc

def z580 : W := mkw 0x80e19a896a829a26 0x4070cd44b5414d13 0x03e3180b60861a66 0x81f18c05b0430d33

def z581 : W := mkw 0x0132001003ac0740 0x0099000801d603a0 0xcfff000003fe07e1 0xe7ff800001ff03f0

def z582 : W := mkw 0x800000012c0000ab 0x4000000096000055 0x7800180ffc811ffe 0xbc000c07fe408fff

def z583 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x3000e7f49c01e598 0x180073fa4e00f2cc

def z584 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1cfffcfff9ff9f 0xfe0e7ffe7ffcffcf

def z585 : W := mkw 0x0932010002f7d800 0x04990080017bec00 0xcfff000003fff801 0xe7ff800001fffc00

def z586 : W := mkw 0x81730b8b2ee70aeb 0x40b985c597738575 0x7fe31f0ffcc71fff 0xbff18f87fe638fff

def z587 : W := mkw 0x12cdfeeff8000000 0x0966ff77fc000000 0x3000fffffc000000 0x18007ffffe000000

def z588 : W := mkw 0x0112000200240040 0x0089000100120020 0x0003000300060060 0x0001800180030030

def z589 : W := mkw 0x00a090100380b614 0x0050480801c05b0a 0xebe0f8000381fe1e 0xf5f07c0001c0ff0f

def z590 : W := mkw 0x0020000002a40240 0x0010000001520120 0x0000000000860260 0x0000000000430130

def z591 : W := mkw 0x0e8dff74955bfd99 0x8746ffba4aadfecc 0xfc1cfff49f79fd99 0x7e0e7ffa4fbcfecc

def z592 : W := mkw 0x0fbbdf1007fffd99 0x87ddef8803fffecc 0xefffff0003fffd99 0xf7ffff8001fffecc

def z593 : W := mkw 0x80412bb9ed432ebf 0x402095dcf6a1975f 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z594 : W := mkw 0x04ccf5fcd5596599 0x82667afe6aacb2cc 0xfffcfffcff79e599 0xfffe7ffe7fbcf2cc

def z595 : W := mkw 0x05fef5fed7fdf7dd 0x82ff7aff6bfefbee 0xffffffffffffffff 0xffffffffffffffff

def z596 : W := mkw 0x0408652094516099 0x820432904a28b04c 0x7c00e7049c41e599 0x3e0073824e20f2cc

def z597 : W := mkw 0x0080900040009004 0x0040480020004802 0x0000180060001806 0x00000c0030000c03

def z598 : W := mkw 0x08210b0002f7d800 0x04108580017bec00 0x6c031f0003fff801 0xb6018f8001fffc00

def z599 : W := mkw 0x04e4b0fcd788b79d 0x8272587e6bc45bce 0xfbe0f8fcff81ff9e 0xfdf07c7e7fc0ffcf

def z600 : W := mkw 0x0bbbff20c2f7f814 0x05ddff90617bfc0a 0xefffff00e3fff81f 0xf7ffff8071fffc0f

def z601 : W := mkw 0x0bfbdf8842f7da04 0x05fdefc4217bed02 0xefffff0863fffa07 0xf7ffff8431fffd03

def z602 : W := mkw 0x0000213085412499 0x0000109842a0924c 0xfc00e7f49f41e599 0x7e0073fa4fa0f2cc

def z603 : W := mkw 0x128dfe65f8000000 0x0946ff32fc000000 0xf01cfff4fc000001 0x780e7ffa7e000000

def z604 : W := mkw 0x00a0b030c380b614 0x0050581861c05b0a 0x2800f800e381fe1e 0x14007c0071c0ff0f

def z605 : W := mkw 0x0080b020c000b014 0x004058106000580a 0x7800f808e081fe1e 0xbc007c047040ff0f

def z606 : W := mkw 0x13fffefffbac0740 0x09ffff7ffdd603a0 0xf3ffffffff380001 0xf9ffffffff9c0000

def z607 : W := mkw 0x13f79adf6bac0740 0x09fbcd6fb5d603a0 0xdfff18ff63fe07e1 0xefff8c7fb1ff03f0

def z608 : W := mkw 0x10002021f8000000 0x08001010fc000000 0x00000000fc000000 0x000000007e000000

def z609 : W := mkw 0x0060009803800600 0x0030004c01c00300 0xfbe018f8e3811e1e 0xfdf00c7c71c08f0f

def z610 : W := mkw 0x0404004414080189 0x820200220a0400c4 0x000000041c000180 0x000000020e0000c0

def z611 : W := mkw 0x104420fff9002614 0x0822107ffc80130a 0x100000fffc00061e 0x0800007ffe00030f

def z612 : W := mkw 0x00e8f5b8c3d1f614 0x00747adc61e8fb0a 0xfffcfff8e3f9fe1f 0xfffe7ffc71fcff0f

def z613 : W := mkw 0x057601de07fd67d9 0x82bb00ef03feb3ec 0xdfff00ff03ffe7f9 0xefff807f81fff3fc

def z614 : W := mkw 0x13fffeeffaa40000 0x09ffff77fd520000 0xfffffffffffe0001 0xffffffffffff0000

def z615 : W := mkw 0x0b7f4fde03ff4f40 0x05bfa7ef01ffa7a0 0xdfff07ff03fe07e1 0xefff83ff81ff03f0

def z616 : W := mkw 0x0000000000000000 0x0000000000000000 0x0800000000811e1e 0x0400000000408f0f

def z617 : W := mkw 0x0000203081002410 0x0000101840801208 0xf800f8f8e381fe1e 0xfc007c7c71c0ff0f

def z618 : W := mkw 0x015600ce00000000 0x00ab006700000000 0xdfff00ff00c607e1 0xefff807f806303f0

def z619 : W := mkw 0x002000100380b614 0x0010000801c05b0a 0x78001808e381fe1e 0xbc000c0471c0ff0f

def z620 : W := mkw 0x0bbbdf1003f7fe14 0x05ddef8801fbff0a 0xefffff0003fffe1f 0xf7ffff8001ffff0f

def z621 : W := mkw 0x171f4f473c594189 0x8b8fa7a39e2ca0c4 0x041f07071c780181 0x020f83838e3c00c0

def z622 : W := mkw 0x002020308380b614 0x0010101841c05b0a 0xf800e0f08381fe1e 0x7c00707841c0ff0f

def z623 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x70031f0ffc01181f 0xb8018f87fe008c0f

def z624 : W := mkw 0x00e0b0a8c2809000 0x0070585461404800 0xfbe0f8f8e381f800 0xfdf07c7c71c0fc00

def z625 : W := mkw 0x13dffefff9002410 0x09efff7ffc801208 0xfbffffffff01e419 0xfdffffffff80f20c

def z626 : W := mkw 0x0bf39a8a02a69a40 0x05f9cd4501534d20 0x03e3180b00861a60 0x81f18c0580430d30

def z627 : W := mkw 0x0020001003acb754 0x0010000801d65baa 0x0c00000003fffffe 0x0600000001ffffff

def z628 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x141c07f49c780599 0x0a0e03fa4e3c02cc

def z629 : W := mkw 0x0000010004410089 0x0000008002208044 0x200007009c010018 0x100003804e00800c

def z630 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x83ff00fb03be0260 0xc1ff807d81df0130

def z631 : W := mkw 0x13dffeeed0000000 0x09efff7768000000 0xe3fffff000000001 0xf1fffff800000000

def z632 : W := mkw 0x0000001001002614 0x000000080080130a 0x000000000000061e 0x000000000000030f

def z633 : W := mkw 0x0408450014514089 0x820422800a28a044 0x000007001c000000 0x000003800e000000

def z634 : W := mkw 0x00c0908840000000 0x0060484420000000 0x03e0180860000000 0x81f00c0430000000

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000f000007e0 0x08000007800003f0

def z636 : W := mkw 0x0bffdfce02f7d800 0x05ffefe7017bec00 0xffffffff03fff801 0xffffffff81fffc00

def z637 : W := mkw 0x00e0908842809204 0x0070484421404902 0x03e0000000000000 0x01f0000000000000

def z638 : W := mkw 0x00c0b0a8c0000000 0x0060585460000000 0x83e0e0f000000000 0x41f0707800000000

def z639 : W := mkw 0x137f4edf3bac0740 0x09bfa76f9dd603a0 0xdfff07ff1ffe07e1 0xefff83ff8fff03f0

def z640 : W := mkw 0x0040008a00000240 0x0020004500000120 0x0000000b00000260 0x0000000580000130

def z641 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xf3e0f8f8e300e000 0xf9f07c7c71807000

def z642 : W := mkw 0x13d2908a40000000 0x09e9484520000000 0x03e0000000000000 0x01f0000000000000

def z643 : W := mkw 0x00010a0128000000 0x0000850094000000 0x20001f00fc000000 0x10000f807e000000

def z644 : W := mkw 0x01f2b0b8c3a4b614 0x00f9585c61d25b0a 0xfffff8f8e3fffe1f 0xfffffc7c71ffff0f

def z645 : W := mkw 0x03bbde0002a40000 0x01ddef0001520000 0xefffff0003fe0001 0xf7ffff8001ff0000

def z646 : W := mkw 0x0a89df000053d800 0x0544ef800029ec00 0x6c03ff0000c7f801 0xb601ff800063fc00

def z647 : W := mkw 0x8a89df012c53d8ab 0x4544ef809629ec55 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z648 : W := mkw 0x13dbfeabf8000000 0x09edff55fc000000 0x23e3ff0bfc000000 0x91f1ff85fe000000

def z649 : W := mkw 0x0080b020c000b014 0x004058106000580a 0x0000e0000000e000 0x0000700000007000

def z650 : W := mkw 0x13d79acf68000000 0x09ebcd67b4000000 0xd3ff18ff60000001 0xe9ff8c7fb0000000

def z651 : W := mkw 0x000c646490000000 0x0006323248000000 0x801ce0f000000000 0x400e707800000000

def z652 : W := mkw 0x0040008800000000 0x0020004400000000 0xd3e000f800000000 0xe9f0007c00000000

def z653 : W := mkw 0x0060009803800600 0x0030004c01c00300 0x83e000f003000000 0x41f0007801800000

def z654 : W := mkw 0x840d6f75bd5b6dbb 0xc206b7badeadb6dd 0xfc1cfff4ff79fd9f 0x7e0e7ffa7fbcfecf

def z655 : W := mkw 0x0000010000410000 0x0000008000208000 0x6c00070000410001 0x3600038000208000

def z656 : W := mkw 0x0488f520d451f09d 0x82447a906a28f84e 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c03180fe0c71fff 0xbe018c07f0638fff

def z658 : W := mkw 0x08a0910002f7d800 0x04504880017bec00 0xefe0f80003fff800 0xf7f07c0001fffc00

def z659 : W := mkw 0x006020b883802610 0x0030105c41c01308 0xfbe0e0f88381e618 0xfdf0707c41c0f30c

def z660 : W := mkw 0x039bdf0000430800 0x01cdef8000218400 0xefffff0000c71801 0xf7ffff8000638c00

def z661 : W := mkw 0x13dffefff9080740 0x09efff7ffc8403a0 0xf3fffffffc0007e1 0xf9fffffffe0003f0

def z662 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0xf3fcf8f8e0000000 0xf9fe7c7c70000000

def z663 : W := mkw 0x139bfe21f8000000 0x09cdff10fc000000 0xe3ffff00fc000001 0xf1ffff807e000000

def z664 : W := mkw 0x00010b0128430800 0x0000858094218400 0x7c031f0ffcc71801 0xbe018f87fe638c00

def z665 : W := mkw 0x004020a8c0000000 0x0020105460000000 0x100000f8e0000000 0x0800007c70000000

def z666 : W := mkw 0x84000110055b6dbb 0xc200008802adb6dd 0x0c00000003fffffe 0x0600000001ffffff

def z667 : W := mkw 0x804400df2d0807eb 0x4022006f968403f5 0x100000fffc0007fe 0x0800007ffe0003ff

def z668 : W := mkw 0x80610b992fc30eab 0x403085cc97e18755 0xffe31fffffc71fff 0xfff18fffffe38fff

def z669 : W := mkw 0x0024005403ac0740 0x0012002a01d603a0 0xdc1c00f403fe07e1 0x6e0e007a01ff03f0

def z670 : W := mkw 0x0000001001080500 0x0000000800840280 0x0c00000003780580 0x0600000001bc02c0

def z671 : W := mkw 0x01f6b0fec380b614 0x00fb587f61c05b0a 0xfbfff8ffe381fe1f 0xfdfffc7ff1c0ff0f

def z672 : W := mkw 0x81570bcf2c4308ab 0x40ab85e796218455 0xffff1ffffcc71fff 0xffff8ffffe638fff

def z673 : W := mkw 0x0008450000514000 0x000422800028a000 0x2000e7000001e000 0x100073800000f000

def z674 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x30001f0ffc011ffe 0x18000f87fe008fff

def z675 : W := mkw 0x00010b0000430800 0x0000858000218400 0x7c031f0f00c71fe1 0xbe018f8780638ff0

def z676 : W := mkw 0x17dffefff9186510 0x8befff7ffc8c3288 0xf3ffffffff38e001 0xf9ffffffff9c7000

def z677 : W := mkw 0x0004004600080140 0x00020023000400a0 0x00000007000001e0 0x00000003800000f0

def z678 : W := mkw 0x840d6f75bd5b6dbb 0xc206b7badeadb6dd 0xfc1fe7f79f7fe5f9 0x7e0ff3fbcfbff2fc

def z679 : W := mkw 0x044c65fe955967d9 0x822632ff4aacb3ec 0xfc1ce7ff9f79e7f9 0x7e0e73ffcfbcf3fc

def z680 : W := mkw 0x0000010004410089 0x0000008002208044 0x0c00000000410598 0x06000000002082cc

def z681 : W := mkw 0x1bfbdf8b6af7d800 0x0dfdefc5b57bec00 0xefffff0b63fff801 0xf7ffff85b1fffc00

def z682 : W := mkw 0x13fef4fed380b614 0x09ff7a7f69c05b0a 0x83fce0f00300e000 0x41fe707801807000

def z683 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x8c1ce0f00379e598 0x460e707801bcf2cc

def z684 : W := mkw 0x00ecf4fcd380b614 0x00767a7e69c05b0a 0xfbfcfffcff81fe1f 0xfdfe7ffe7fc0ff0f

def z685 : W := mkw 0x1bffffeed2f7d800 0x0dfffff7697bec00 0xeffffff003fff801 0xf7fffff801fffc00

def z686 : W := mkw 0x0132000002a40000 0x0099000001520000 0x03e3000000860000 0x81f1800000430000

def z687 : W := mkw 0x90452beffc4308ab 0x482295f7fe218455 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z688 : W := mkw 0x0fbfdf4416ffd989 0x87dfefa20b7fecc4 0xefffff041ffff981 0xf7ffff820ffffcc0

def z689 : W := mkw 0x135f6eeff8000000 0x09afb777fc000000 0x101f07fffc000001 0x080f83fffe000000

def z690 : W := mkw 0x0400213085596599 0x8200109842acb2cc 0xfc00e0f08379e598 0x7e00707841bcf2cc

def z691 : W := mkw 0x00c0b0b8c100b614 0x0060585c60805b0a 0x3000f8f8e001fe1e 0x18007c7c7000ff0f

def z692 : W := mkw 0x040d6f74955b6d99 0x8206b7ba4aadb6cc 0xfc1ffff49ffffd99 0xfe0ffffa4ffffecc

def z693 : W := mkw 0x0bfffffec3ffff54 0x05ffffff61ffffaa 0xffffffffe3ffffff 0xfffffffff1ffffff

def z694 : W := mkw 0x00e090984380b614 0x0070484c21c05b0a 0x0be018086381fe1e 0x85f00c0431c0ff0f

def z695 : W := mkw 0x004020b8c1002614 0x0020105c6080130a 0xf800e0f8e301e61e 0x7c00707c7180f30f

def z696 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x8be0e0f00381fe1e 0x45f0707801c0ff0f

def z697 : W := mkw 0x104420fff9080740 0x0822107ffc8403a0 0x100000fffc0007e0 0x0800007ffe0003f0

def z698 : W := mkw 0x104c64eff8000000 0x08263277fc000000 0xf01ce7fffc000001 0x780e73fffe000000

def z699 : W := mkw 0x0020001003800600 0x0010000801c00300 0x0800000003800600 0x0400000001c00300

def z700 : W := mkw 0x04ecf4fcd398f714 0x82767a7e69cc7b8a 0x83fce0f00338e000 0x41fe7078019c7000

def z701 : W := mkw 0x0e89ff209453f899 0x8744ff904a29fc4c 0x2000ff009c01f818 0x10007f804e00fc0c

def z702 : W := mkw 0x12819a0168000000 0x0940cd00b4000000 0x0000180060000000 0x00000c0030000000

def z703 : W := mkw 0x0a89df000053d800 0x0544ef800029ec00 0xec1cff000379f801 0x760e7f8001bcfc00

def z704 : W := mkw 0x0b130a0000260800 0x0589850000130400 0x0003000000060000 0x0001800000030000

def z705 : W := mkw 0x00010a0128000000 0x0000850094000000 0x000307071c000001 0x000183838e000000

def z706 : W := mkw 0x8000000000020822 0x4000000000010411 0x0000000000861a66 0x0000000000430d33

def z707 : W := mkw 0x8bbbdf0002f7d822 0x45ddef80017bec11 0xefffff0003fffa67 0xf7ffff8001fffd33

def z708 : W := mkw 0x13dffeeff800b014 0x09efff77fc00580a 0xf3fffffffc00e001 0xf9fffffffe007000

def z709 : W := mkw 0x03bbdf0002d1d000 0x01ddef800168e800 0xefffff0003f9f801 0xf7ffff8001fcfc00

def z710 : W := mkw 0x057a65aa96f562d9 0x82bd32d54b7ab16c 0x23e3e70b9c87e278 0x91f1f385ce43f13c

def z711 : W := mkw 0x0420011007fd47c9 0x8210008803fea3e4 0x0c00000003fe07e0 0x0600000001ff03f0

def z712 : W := mkw 0x00c1baa9e8000000 0x0060dd54f4000000 0xf3e0fff8fc000000 0xf9f07ffc7e000000

def z713 : W := mkw 0x17d39b9b6d596599 0x8be9cdcdb6acb2cc 0x0fe3180b6379e598 0x87f18c05b1bcf2cc

def z714 : W := mkw 0x0fbbdf0016f7d889 0x87ddef800b7bec44 0xefffff001ffff801 0xf7ffff800ffffc00

def z715 : W := mkw 0x104420fff9082754 0x0822107ffc8413aa 0x100000fffc0007fe 0x0800007ffe0003ff

def z716 : W := mkw 0x00e0b0a8c280b214 0x007058546140590a 0xf3e0f8f8e081fa1e 0xf9f07c7c7040fd0f

def z717 : W := mkw 0x0bbbde0002b4d000 0x05ddef00015a6800 0xa3fcff000338e000 0x51fe7f80019c7000

def z718 : W := mkw 0x006020b883802610 0x0030105c41c01308 0xfbe0f8f8e381fe1e 0xfdf07c7c71c0ff0f

def z719 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe0f8f0e301fc1e 0x7df07c787180fe0f

def z720 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xac1ce7f09f79e598 0x560e73f84fbcf2cc

def z721 : W := mkw 0x840d6e75b91a6d32 0xc206b73adc8d3699 0x801ff8fb63befa66 0xc00ffc7db1df7d33

def z722 : W := mkw 0x10c5baeff8000000 0x0862dd77fc000000 0xf3e3fffffc000001 0xf9f1fffffe000000

def z723 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xcfffe70003fee001 0xe7fff38001ff7000

def z724 : W := mkw 0x006400dc03880700 0x0032006e01c40380 0xdfff00ff03fe07e1 0xefff807f81ff03f0

def z725 : W := mkw 0x0196b066c02cb154 0x00cb5833601658aa 0x241ff807e07ff9ff 0x120ffc03f03ffcff

def z726 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf7fffffffc4601e1 0xfbfffffffe2300f0

def z727 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1ce7f49ff9ff9f 0x7e0e73fa4ffcffcf

def z728 : W := mkw 0x1bdffeeff8029800 0x0defff77fc014c00 0xf3fffffffc001801 0xf9fffffffe000c00

def z729 : W := mkw 0x040c647495186599 0x8206323a4a8c32cc 0xf01ce7f49f38e599 0x780e73fa4f9c72cc

def z730 : W := mkw 0x0bbad50002f5d000 0x05dd6a80017ae800 0x87fce7000378e001 0x43fe738001bc7000

def z731 : W := mkw 0x12a9fe31fbac0740 0x0954ff18fdd603a0 0x2c00ff00fffe07e0 0x16007f807fff03f0

def z732 : W := mkw 0x01b39b0002e79800 0x00d9cd800173cc00 0xefffff0003fff801 0xf7ffff8001fffc00

def z733 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1cfff4ff79fd9f 0x7e0e7ffa7fbcfecf

def z734 : W := mkw 0x13dbfea9f8000000 0x09edff54fc000000 0xf3fffff8fc000001 0xf9fffffc7e000000

def z735 : W := mkw 0x8bbbdf012af7d822 0x45ddef80957bec11 0xefffff0303fff861 0xf7ffff8181fffc30

def z736 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xffe3f8f8e3c7fe1f 0xfff1fc7c71e3ff0f

def z737 : W := mkw 0x040c6574955b6d99 0x820632ba4aadb6cc 0xfc1ce7f49ffffd99 0x7e0e73fa4ffffecc

def z738 : W := mkw 0x0136005603ac0540 0x009b002b01d602a0 0xdfff00f703fe05e1 0xefff807b81ff02f0

def z739 : W := mkw 0x013a440002b44000 0x009d2200015a2000 0xcfffe00003fee001 0xe7fff00001ff7000

def z740 : W := mkw 0x039ffe65b8000000 0x01cfff32dc000000 0xf3fffffffc000001 0xf9fffffffe000000

def z741 : W := mkw 0x0b3b4f0002f74800 0x059da780017ba400 0xefffe70003ffe001 0xf7fff38001fff000

def z742 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xffffe0ff03ffe7e1 0xfffff07f81fff3f0

def z743 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xe3fcf8000338e000 0xf1fe7c00019c7000

def z744 : W := mkw 0x12a9fe31fb80b614 0x0954ff18fdc05b0a 0x2800ff00ff81fe1e 0x14007f807fc0ff0f

def z745 : W := mkw 0x139ffe65f8000000 0x09cfff32fc000000 0xf3fffff4fc000001 0xf9fffffa7e000000

def z746 : W := mkw 0x13dffeeff8240000 0x09efff77fc120000 0xf7fffffffc7e0001 0xfbfffffffe3f0000

def z747 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3ffe7f79c000001 0x79fff3fbce000000

def z748 : W := mkw 0x8b1f4f472c7f49eb 0x458fa7a3963fa4f5 0x041f07071c7e01e1 0x020f83838e3f00f0

def z749 : W := mkw 0x000c647491082510 0x0006323a48841288 0xfc1ce7f49f79e599 0x7e0e73fa4fbcf2cc

def z750 : W := mkw 0x13dffeeff8020800 0x09efff77fc010400 0xf3fffffffc861801 0xf9fffffffe430c00

def z751 : W := mkw 0x186421effaf7d800 0x0c3210f7fd7bec00 0x1c0000fffffff800 0x0e00007ffffffc00

def z752 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff0083fffc19 0xffffff8041fffe0c

def z753 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xffff18ffe3fe07e1 0xffff8c7ff1ff03f0

def z754 : W := mkw 0x80e1bbb9efc3bebf 0x4070dddcf7e1df5f 0x87e3e7f71f46e1e1 0x43f1f3fb8fa370f0

def z755 : W := mkw 0x851f4f473c7f49eb 0xc28fa7a39e3fa4f5 0x041f07071c7e01e1 0x020f83838e3f00f0

def z756 : W := mkw 0x044420fe950827d9 0x8222107f4a8413ec 0x100000f49c000598 0x0800007a4e0002cc

def z757 : W := mkw 0x8bbbdf012af7d822 0x45ddef80957bec11 0xefffff0063fff807 0xf7ffff8031fffc03

def z758 : W := mkw 0x0b9bdf000053d800 0x05cdef800029ec00 0xefffff000379f801 0xf7ffff8001bcfc00

def z759 : W := mkw 0x135f4ecf38000000 0x09afa7679c000000 0xf3ff1ffffc000001 0xf9ff8ffffe000000

def z760 : W := mkw 0x8420011007dbffbf 0xc210008803edffdf 0x0c00000003fffffe 0x0600000001ffffff

def z761 : W := mkw 0x81770bdf2fef0feb 0x40bb85ef97f787f5 0xa3fc1ff0ff39181e 0x51fe0ff87f9c8c0f

def z762 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x8ffff80003fff800 0xc7fffc0001fffc00

def z763 : W := mkw 0x004c64ec90000000 0x0026327648000000 0xf3fce7fc9c000001 0xf9fe73fe4e000000

def z764 : W := mkw 0x013b4f0002f74800 0x009da780017ba400 0xefffff0003fff801 0xf7ffff8001fffc00

def z765 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfffffffffcc60001 0xfffffffffe630000

def z766 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe0f8ffe381fffe 0xfdf07c7ff1c0ffff

def z767 : W := mkw 0x0acddfde015bdf40 0x0566efef00adefa0 0x3000ffff0001ffe0 0x18007fff8000fff0

def z768 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdfff00f7037e05e1 0x6fff807b81bf02f0

def z769 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x30031f0ffc871ffe 0x98018f87fe438fff

def z770 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fffffffc00061f 0xf9fffffffe00030f

def z771 : W := mkw 0x0bbad50002f7d800 0x05dd6a80017bec00 0x83fce0000339f800 0x41fe7000019cfc00

def z772 : W := mkw 0x0fb7ba7497aebd99 0x87dbdd3a4bd75ecc 0x13e318f49c861d98 0x89f18c7a4e430ecc

def z773 : W := mkw 0x00210a112bac0740 0x0010850895d603a0 0x7c031f0ffffe07e1 0xbe018f87ffff03f0

def z774 : W := mkw 0x8bbad4012eb4d0ab 0x45dd6a00975a6855 0x93fce00fff38e7fe 0x49fe7007ff9c73ff

def z775 : W := mkw 0x01def4eed0000000 0x00ef7a7768000000 0xf3fffffffc000001 0xf9fffffffe000000

def z776 : W := mkw 0x8020011007efbfff 0x4010008803f7dfff 0x0c00000003fffffe 0x0600000001ffffff

def z777 : W := mkw 0x8bf39a896aa69a26 0x45f9cd44b5534d13 0x03e3180b60861a66 0x81f18c05b0430d33

def z778 : W := mkw 0x0bbad40002b6d800 0x05dd6a00015b6c00 0x83fce00003bef800 0x41fe700001df7c00

def z779 : W := mkw 0x9bf39a8b6aa69822 0x4df9cd45b5534c11 0x03e3180b60861a66 0x81f18c05b0430d33

def z780 : W := mkw 0x93def5eed44308ab 0x49ef7af76a218455 0x8ffce0f000c71ffe 0x47fe707800638fff

def z781 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fcfff8fc000000 0xf9fe7ffc7e000000

def z782 : W := mkw 0x017600ce02ac0140 0x00bb0067015600a0 0xdfff00ff03fe01e1 0xefff807f81ff00f0

def z783 : W := mkw 0x13d79acf68000000 0x09ebcd67b4000000 0xf3ff1ffffc000001 0xf9ff8ffffe000000

def z784 : W := mkw 0x80a9df012ed3d8ab 0x4054ef809769ec55 0xffffff0fffffffff 0xffffff87ffffffff

def z785 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xebfce0000339e000 0x75fe7000019cf000

def z786 : W := mkw 0x135f6eeff8000000 0x09afb777fc000000 0xd3ff07fffc000001 0xe9ff83fffe000000

def z787 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1fe7f79f7fe5f9 0x7e0ff3fbcfbff2fc

def z788 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff071fffffff 0xf7ffff838fffffff

def z789 : W := mkw 0x0bbbde0002b6d800 0x05ddef00015b6c00 0xcffff80003fef801 0xe7fffc0001ff7c00

def z790 : W := mkw 0x8f1f4f453c7f49ab 0xc78fa7a29e3fa4d5 0x041f07071c7e01e1 0x020f83838e3f00f0

def z791 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x801ce7f01f38e000 0x400e73f80f9c7000

def z792 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xd7ff00ff037e01e1 0xebff807f81bf00f0

def z793 : W := mkw 0x00c0b0a8c0000000 0x0060585460000000 0xf3e0fffcfc000001 0xf9f07ffe7e000000

def z794 : W := mkw 0x00e0b0b8c3acb754 0x0070585c61d65baa 0xffe3f8ffe3ffffff 0xfff1fc7ff1ffffff

def z795 : W := mkw 0x13fef4fed3acb754 0x09ff7a7f69d65baa 0x83fce0f00338e000 0x41fe7078019c7000

def z796 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0x87ffe000037ee001 0x43fff00001bf7000

def z797 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0x83fcf80003b8f800 0xc1fe7c0001dc7c00

def z798 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x941ce7f49f78e599 0x4a0e73fa4fbc72cc

def z799 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0x83ffe00003bee000 0xc1fff00001df7000

def z800 : W := mkw 0x840c6574955b6dbb 0xc20632ba4aadb6dd 0xfc1ce7f49f79fd9f 0x7e0e73fa4fbcfecf

def z801 : W := mkw 0x0420011007fdf7dd 0x8210008803fefbee 0x0c00000003fffffe 0x0600000001ffffff

def z802 : W := mkw 0x13dffeeff8002010 0x09efff77fc001008 0xf3fffffffc01e019 0xf9fffffffe00f00c

def z803 : W := mkw 0x0bbbde0002b4d000 0x05ddef00015a6800 0x83ffe7000338e001 0x41fff380019c7000

def z804 : W := mkw 0x044420fe95082599 0x8222107f4a8412cc 0x100000ff9c000598 0x0800007fce0002cc

def z805 : W := mkw 0x00a8d50006d1d089 0x00546a800368e844 0xfffcff0cfff9ff9f 0xfffe7f867ffcffcf

def z806 : W := mkw 0x0088d50000514000 0x00446a800028a000 0xeffcff000379e001 0xf7fe7f8001bcf000

def z807 : W := mkw 0x8820011007f7febf 0x4410008803fbff5f 0x0c00000003fffffe 0x0600000001ffffff

def z808 : W := mkw 0x00c0b0b8c100b414 0x0060585c60805a0a 0xfbe0f8f8e301fc1e 0xfdf07c7c7180fe0f

def z809 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff08fffffe1f 0xffffff847fffff0f

def z810 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x17ff00ff00fe07e1 0x8bff807f807f03f0

def z811 : W := mkw 0x000c656494514089 0x000632b24a28a044 0xfc1ce7f49f79e599 0x7e0e73fa4fbcf2cc

def z812 : W := mkw 0x044420fcd1082714 0x8222107e6884138a 0x000000f000000000 0x0000007800000000

def z813 : W := mkw 0x0b5b6fb8c1776e14 0x05adb7dc60bbb70a 0x141f07f8e07e061f 0x0a0f83fc703f030f

def z814 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xabe0f8f0e381fe1e 0x55f07c7871c0ff0f

def z815 : W := mkw 0x13dbfeabf8000000 0x09edff55fc000000 0xf3e3fffbfc000000 0xf9f1fffdfe000000

def z816 : W := mkw 0x017600de03acb754 0x00bb006f01d65baa 0xdfff00ff03fee7e1 0xefff807f81ff73f0

def z817 : W := mkw 0x00410a8928000000 0x0020854494000000 0xf3e31ffffc000001 0xf9f18ffffe000000

def z818 : W := mkw 0x81b39b012ee798ab 0x40d9cd809773cc55 0xffffff0fffffffff 0xffffff87ffffffff

def z819 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1fffffffffffff 0xfe0fffffffffffff

def z820 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xffffffffff780001 0xffffffffffbc0000

def z821 : W := mkw 0x000c455405594589 0x000622aa02aca2c4 0xfc1ce7f49f79e599 0x7e0e73fa4fbcf2cc

def z822 : W := mkw 0x8bbbdf0006f7d8ab 0x45ddef80037bec55 0xefffff0003fff81f 0xf7ffff8001fffc0f

def z823 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff0f1fffffe1 0xffffff878ffffff0

def z824 : W := mkw 0x93dffeeff8020822 0x49efff77fc010411 0xf3fffffffc060061 0xf9fffffffe030030

def z825 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1cfff49ff9fd99 0xfe0e7ffa4ffcfecc

def z826 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfbfffffffc010419 0xfdfffffffe00820c

def z827 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xaffcff0003fff800 0x57fe7f8001fffc00

def z828 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xc3ffe0000338e001 0xe1fff000019c7000

def z829 : W := mkw 0x0408653095516499 0x820432984aa8b24c 0xfc1ce7f09f79e419 0x7e0e73f84fbcf20c

def z830 : W := mkw 0x133f4e573b80b614 0x099fa72b9dc05b0a 0x081f07071f81fe1f 0x040f83838fc0ff0f

def z831 : W := mkw 0x044420fe91082750 0x8222107f488413a8 0x100000ff000007e0 0x0800007f800003f0

def z832 : W := mkw 0x8820011007ffdfeb 0x4410008803ffeff5 0x0c00000003fffffe 0x0600000001ffffff

def z833 : W := mkw 0x040c455415594589 0x820622aa0aaca2c4 0xfc1ce7f41f79e581 0x7e0e73fa0fbcf2c0

def z834 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff0b63ffffff 0xf7ffff85b1ffffff

def z835 : W := mkw 0x00c0b0b8c100b614 0x0060585c60805b0a 0xf3e0f8f8e001fe1e 0xf9f07c7c7000ff0f

def z836 : W := mkw 0x00e0b0a8c280b014 0x007058546140580a 0xfbe0f8f8e381f81e 0xfdf07c7c71c0fc0f

def z837 : W := mkw 0x039ad40000104000 0x01cd6a0000082000 0x83fce0000338e000 0x41fe7000019c7000

def z838 : W := mkw 0x044420fcd508279d 0x8222107e6a8413ce 0x100000f49c000598 0x0800007a4e0002cc

def z839 : W := mkw 0x017600ce02a40000 0x00bb006701520000 0xdfff00ff03fe07e1 0xefff807f81ff03f0

def z840 : W := mkw 0x000c657491516410 0x000632ba48a8b208 0xfc1ce7f49f79e419 0x7e0e73fa4fbcf20c

def z841 : W := mkw 0x135f6eefb8000000 0x09afb777dc000000 0xf3ffe7ff9c000001 0xf9fff3ffce000000

def z842 : W := mkw 0x12cdfeedf8000000 0x0966ff76fc000000 0xf3fcfffcfc000001 0xf9fe7ffe7e000000

def z843 : W := mkw 0x017600de03ac2750 0x00bb006f01d613a8 0xdfff00ff03ffe7f9 0xefff807f81fff3fc

def z844 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1fe7ff9f79e599 0xfe0ff3ffcfbcf2cc

def z845 : W := mkw 0x0bbbdf012af7d800 0x05ddef80957bec00 0xefffff00fffff801 0xf7ffff807ffffc00

def z846 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff00e3fff81f 0xf7ffff8071fffc0f

def z847 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdfff18ff63fe1fe7 0xefff8c7fb1ff0ff3

def z848 : W := mkw 0x0bbad50002f7d800 0x05dd6a80017bec00 0xeffcf80003fff800 0xf7fe7c0001fffc00

def z849 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x33e0f8f8e081fe1e 0x99f07c7c7040ff0f

def z850 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xebe0f8f0e381f81e 0xf5f07c7871c0fc0f

def z851 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff0ffffff81f 0xffffff87fffffc0f

def z852 : W := mkw 0x8c20011007fffdbb 0xc610008803fffedd 0x0c00000003fffffe 0x0600000001ffffff

def z853 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff0b03fffa61 0xf7ffff8581fffd30

def z854 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fffffffc860261 0xf9fffffffe430130

def z855 : W := mkw 0x00a0b0308380b410 0x0050581841c05a08 0xfbe0f8f8e381fe1e 0xfdf07c7c71c0ff0f

def z856 : W := mkw 0x0132000002a40000 0x0099000001520000 0xefffe00003ffe001 0xf7fff00001fff000

def z857 : W := mkw 0x0bbbdf0042f7d804 0x05ddef80217bec02 0xefffff0063fff807 0xf7ffff8031fffc03

def z858 : W := mkw 0x80c0b1a8c44308ab 0x406058d462218455 0xffe0f8f8e0c71ffe 0xfff07c7c70638fff

def z859 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff0bfffffa7f 0xf7ffff85fffffd3f

def z860 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xebfcff0003b9f800 0xf5fe7f8001dcfc00

def z861 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffe700037fe001 0x77fff38001bff000

def z862 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xf41ce7f49f78e181 0x7a0e73fa4fbc70c0

def z863 : W := mkw 0x0bbbdf012af7d800 0x05ddef80957bec00 0xefffff071ffff801 0xf7ffff838ffffc00

def z864 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xeffcff000379f801 0x77fe7f8001bcfc00

def z865 : W := mkw 0x13dffeeff8080140 0x09efff77fc0400a0 0xf3fffffffc0001e1 0xf9fffffffe0000f0

def z866 : W := mkw 0x0bbbdf0006f7d889 0x05ddef80037bec44 0xefffff0003fffd99 0xf7ffff8001fffecc

def z867 : W := mkw 0x0008653085516499 0x0004329842a8b24c 0xfc1ce7f49f79e599 0x7e0e73fa4fbcf2cc

def z868 : W := mkw 0x05fef4fed3bcf754 0x82ff7a7f69de7baa 0x83fce0f00338e000 0x41fe7078019c7000

def z869 : W := mkw 0x17dffeeff8106010 0x8befff77fc083008 0xf3fffffffc00e001 0xf9fffffffe007000

def z870 : W := mkw 0x0bbad50002f5d000 0x05dd6a80017ae800 0xa3fce7000339e000 0x51fe7380019cf000

def z871 : W := mkw 0x144420fed5082599 0x8a22107f6a8412cc 0x100000f49c000598 0x0800007a4e0002cc

def z872 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xa3fffff7fc000001 0x51fffffbfe000000

def z873 : W := mkw 0x040c647491186510 0x8206323a488c3288 0x801ce7f41f38e001 0x400e73fa0f9c7000

def z874 : W := mkw 0x03bbdf0002f54000 0x01ddef80017aa000 0xefffff0003ffe001 0xf7ffff8001fff000

def z875 : W := mkw 0x015600de01080500 0x00ab006f00840280 0xdfff00ff03fe07e1 0xefff807f81ff03f0

def z876 : W := mkw 0x8bbbdf0006f7d8ab 0x45ddef80037bec55 0xffffff049fffffff 0xffffff824fffffff

def z877 : W := mkw 0x0bbbde012ab4d000 0x05ddef00955a6800 0xf3ffff0fff38e001 0xf9ffff87ff9c7000

def z878 : W := mkw 0x01d7baefe8000000 0x00ebdd77f4000000 0xf3fffffffc000001 0xf9fffffffe000000

def z879 : W := mkw 0x13dffeeff82c0140 0x09efff77fc1600a0 0xf3fffffffc380001 0xf9fffffffe1c0000

def z880 : W := mkw 0x8489ff21fc53f8bf 0xc244ff90fe29fc5f 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z881 : W := mkw 0x04ecd5cc56d9d38d 0x82766ae62b6ce9c6 0x07fc1f0c7cf81b87 0x83fe0f863e7c0dc3

def z882 : W := mkw 0x00c0b0a8c000b014 0x006058546000580a 0xa3e0f8f0e001f81e 0x51f07c787000fc0f

def z883 : W := mkw 0x10ccf4eff8000000 0x08667a77fc000000 0xf3fcfffffc000001 0xf9fe7ffffe000000

def z884 : W := mkw 0x17dffeeff8184100 0x8befff77fc0c2080 0xf3fffffffc380001 0xf9fffffffe1c0000

def z885 : W := mkw 0x03dbfea9e8000000 0x01edff54f4000000 0xf3fffffffc000001 0xf9fffffffe000000

def z886 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x8fff00f703fe07e1 0x47ff807b81ff03f0

def z887 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xdc1ce7f41f78e581 0x6e0e73fa0fbc72c0

def z888 : W := mkw 0x03dffeecd0000000 0x01efff7668000000 0xf3fffffcfc000001 0xf9fffffe7e000000

def z889 : W := mkw 0x0bbbdf0002f5d000 0x05ddef80017ae800 0xefffff000379e001 0xf7ffff8001bcf000

def z890 : W := mkw 0x0c20011007fdf599 0x8610008803fefacc 0x0c0000000379e598 0x0600000001bcf2cc

def z891 : W := mkw 0x12c9fea9f8000000 0x0964ff54fc000000 0xf3e3fffffc000001 0xf9f1fffffe000000

def z892 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0xf3fcfffcfc000001 0xf9fe7ffe7e000000

def z893 : W := mkw 0x011e646490000000 0x008f323248000000 0xf3ffe7f49c000001 0xf9fff3fa4e000000

def z894 : W := mkw 0x0020011007ed07c9 0x0010008803f683e4 0x0c00000003ff07f8 0x0600000001ff83fc

def z895 : W := mkw 0x0bbbde0002b4d000 0x05ddef00015a6800 0xefffff0003fee001 0xf7ffff8001ff7000

def z896 : W := mkw 0x01b2900002a49000 0x00d9480001524800 0xebfcf80003b9f800 0xf5fe7c0001dcfc00

def z897 : W := mkw 0x80010b012c5348ab 0x400085809629a455 0x7c031f0fffffffff 0xbe018f87ffffffff

def z898 : W := mkw 0x017600de03ac2754 0x00bb006f01d613aa 0xdfff00ff03fe07ff 0xefff807f81ff03ff

def z899 : W := mkw 0x00e0b0b8c3a4b614 0x0070585c61d25b0a 0xffe0f8f8e3fffe1e 0xfff07c7c71ffff0f

def z900 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xffff07ff9ffe07e1 0xffff83ffcfff03f0

def z901 : W := mkw 0x00e0b0a8c2809000 0x0070585461404800 0xfbe0f8f8e381fe1e 0xfdf07c7c71c0ff0f

def z902 : W := mkw 0x03dfdecf28000000 0x01efef6794000000 0xf3fffffffc000001 0xf9fffffffe000000

def z903 : W := mkw 0x015e44ce10000000 0x00af226708000000 0xd3ff07ff1c000001 0xe9ff83ff8e000000

def z904 : W := mkw 0x0172009803a40600 0x00b9004c01d20300 0xdfff00ff03fe07e1 0xefff807f81ff03f0

def z905 : W := mkw 0x00e0909803809600 0x0070484c01c04b00 0xfbe0f8f8e381fe1e 0xfdf07c7c71c0ff0f

def z906 : W := mkw 0x00010a0128000000 0x0000850094000000 0x7c031f0ffcc71fff 0xbe018f87fe638fff

def z907 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff079ffffdf9 0xffffff83cffffefc

def z908 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xe3fce7000338e001 0x71fe7380019c7000

def z909 : W := mkw 0x013a440002b44000 0x009d2200015a2000 0x83fce0000338e000 0x41fe7000019c7000

def z910 : W := mkw 0x13dffeeff8009000 0x09efff77fc004800 0xf3fffffffc01f801 0xf9fffffffe00fc00

def z911 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x87ff00ff03fe03e1 0xc3ff807f81ff01f0

def z912 : W := mkw 0x840c6574955b6dbb 0xc20632ba4aadb6dd 0xfc1fe7ff9fffffff 0xfe0ff3ffcfffffff

def z913 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xffe0f8fce3c1ff9f 0xfff07c7e71e0ffcf

def z914 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfffffffffc400581 0xfffffffffe2002c0

def z915 : W := mkw 0x8a89ff21ec53f8bf 0x4544ff90f629fc5f 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z916 : W := mkw 0x13dfdecf78000000 0x09efef67bc000000 0xd3ff1fff7c000001 0xe9ff8fffbe000000

def z917 : W := mkw 0x8bbbdf0006f7d8ab 0x45ddef80037bec55 0xffffff08e3ffffff 0xffffff8471ffffff

def z918 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff0803fffe01 0xffffff8401ffff00

def z919 : W := mkw 0x804420ffed0827ff 0x4022107ff68413ff 0x100000fffc0007fe 0x0800007ffe0003ff

def z920 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x93ffe7fffc000001 0x49fff3fffe000000

def z921 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x33e3fffffc000000 0x99f1fffffe000000

def z922 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1ce7fc9ff9e799 0xfe0e73fe4ffcf3cc

def z923 : W := mkw 0x12c9fea9f8000000 0x0964ff54fc000000 0xa3e0fff0fc000000 0x51f07ff87e000000

def z924 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x8fffe70003fff801 0x47fff38001fffc00

def z925 : W := mkw 0x000c657491594500 0x000632ba48aca280 0xfc1ce7f49f79e581 0x7e0e73fa4fbcf2c0

def z926 : W := mkw 0x144420fffd08279d 0x8a22107ffe8413ce 0x100000fffc00079e 0x0800007ffe0003cf

def z927 : W := mkw 0x133f4e573bac0740 0x099fa72b9dd603a0 0x0c1f07071ffe07e1 0x060f83838fff03f0

def z928 : W := mkw 0x00e0b0b8c3acb754 0x0070585c61d65baa 0xfbe0f8f8e3b9fe1e 0xfdf07c7c71dcff0f

def z929 : W := mkw 0x81f39a8b6aa69a66 0x40f9cd45b5534d33 0x03e3180b60861a66 0x81f18c05b0430d33

def z930 : W := mkw 0x139ffe67b8000000 0x09cfff33dc000000 0xf3fffff79c000001 0xf9fffffbce000000

def z931 : W := mkw 0x1bf39a8b6aa49000 0x0df9cd45b5524800 0x03e3180b60000000 0x81f18c05b0000000

def z932 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfbffffffff01e001 0xfdffffffff80f000

def z933 : W := mkw 0x0bbbde0002b6d800 0x05ddef00015b6c00 0xebfff80003bff800 0xf5fffc0001dffc00

def z934 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdfff00ffe3fe07ff 0xefff807ff1ff03ff

def z935 : W := mkw 0x8420011007ff6ffb 0xc210008803ffb7fd 0x0c00000003fffffe 0x0600000001ffffff

def z936 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff049ffff801 0xffffff824ffffc00

def z937 : W := mkw 0x00e0b0bac380b654 0x0070585d61c05b2a 0xfbe0f8fbe381fe7e 0xfdf07c7df1c0ff3f

def z938 : W := mkw 0x13dffeeff800b014 0x09efff77fc00580a 0xfbfffffffc81fe1f 0xfdfffffffe40ff0f

def z939 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xa3fcf8000339f800 0x51fe7c00019cfc00

def z940 : W := mkw 0x015600ce002c0140 0x00ab0067001600a0 0xdfff00ff00fe07e1 0xefff807f807f03f0

def z941 : W := mkw 0x84452bffbd4b2ffb 0xc22295ffdea597fd 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z942 : W := mkw 0x040c656494594189 0x820632b24a2ca0c4 0xfc1ce7f49f79e181 0x7e0e73fa4fbcf0c0

def z943 : W := mkw 0x004420fec1082754 0x0022107f608413aa 0x100000ff000007e0 0x0800007f800003f0

def z944 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0x8be0f8f86381fe1e 0xc5f07c7c31c0ff0f

def z945 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe3f8ffe381fe1f 0xfdf1fc7ff1c0ff0f

def z946 : W := mkw 0x015600de012c0740 0x00ab006f009603a0 0xd7ff00ff007e07e1 0xebff807f803f03f0

def z947 : W := mkw 0x00a0b030c380b414 0x0050581861c05a0a 0xfbe0f8f0e381fc1e 0xfdf07c7871c0fe0f

def z948 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xa41ce7f49f79e199 0x520e73fa4fbcf0cc

def z949 : W := mkw 0x8bbbdf012af7d822 0x45ddef80957bec11 0xffffff0be3fffe7f 0xffffff85f1ffff3f

def z950 : W := mkw 0x00e0b0b8c3a4b654 0x0070585c61d25b2a 0xfbe0f8f8e387fe7e 0xfdf07c7c71c3ff3f

def z951 : W := mkw 0x80010a012c0208ab 0x4000850096010455 0x70031f0ffc861fff 0xb8018f87fe430fff

def z952 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfffffffffcc71fff 0xfffffffffe638fff

def z953 : W := mkw 0x040c6574d559659d 0x820632ba6aacb2ce 0xfc1ce7f4ff79e59f 0x7e0e73fa7fbcf2cf

def z954 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xe3fffff71c000001 0xf1fffffb8e000000

def z955 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xe7ffff00037ee001 0xf3ffff8001bf7000

def z956 : W := mkw 0x9a89ff21fc53d8ab 0x4d44ff90fe29ec55 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z957 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x13ff1ffffc000001 0x89ff8ffffe000000

def z958 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xf01ce7f49f39e019 0x780e73fa4f9cf00c

def z959 : W := mkw 0x8e89ff21bc53f8bb 0xc744ff90de29fc5d 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z960 : W := mkw 0x044420fcd1082714 0x8222107e6884138a 0x100000f8e000061e 0x0800007c7000030f

def z961 : W := mkw 0x0136005403ac0500 0x009b002a01d60280 0xdfff00ff03fe07e1 0xefff807f81ff03f0

def z962 : W := mkw 0x00ccf4ecd0000000 0x00667a7668000000 0xf3fce7f49c000001 0x79fe73fa4e000000

def z963 : W := mkw 0x017600de43ac0744 0x00bb006f21d603a2 0xdfff00ff63fe07e7 0xefff807fb1ff03f3

def z964 : W := mkw 0x971f4f473c5b49ab 0xcb8fa7a39e2da4d5 0x041f07071c7e01e1 0x020f83838e3f00f0

def z965 : W := mkw 0x0aa9df0002d3d800 0x0554ef800169ec00 0xeffcff0003f9f801 0xf7fe7f8001fcfc00

def z966 : W := mkw 0x00a9df0002d3d800 0x0054ef800169ec00 0xefffff0003fff801 0xf7ffff8001fffc00

def z967 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1ce7fcff79e79f 0x7e0e73fe7fbcf3cf

def z968 : W := mkw 0x00210a112b80b614 0x0010850895c05b0a 0x78031f0fff81fe1f 0xbc018f87ffc0ff0f

def z969 : W := mkw 0x13d7baeff8000000 0x09ebdd77fc000000 0x73e31ffffc000001 0xb9f18ffffe000000

def z970 : W := mkw 0x144420fffd0827d9 0x8a22107ffe8413ec 0x100000fffc0007f8 0x0800007ffe0003fc

def z971 : W := mkw 0x040c656494516099 0x820632b24a28b04c 0xfc1ce7f49f79e019 0x7e0e73fa4fbcf00c

def z972 : W := mkw 0x0bbad50006f5d089 0x05dd6a80037ae844 0xfffce7049f79e599 0x7ffe73824fbcf2cc

def z973 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x83ffffff7c000001 0xc1ffffffbe000000

def z974 : W := mkw 0x1bbbdf032af7d800 0x0dddef81957bec00 0xefffff0303fff801 0xf7ffff8181fffc00

def z975 : W := mkw 0x815601ce044308ab 0x40ab00e702218455 0xdfff00ff00c71fff 0xefff807f80638fff

def z976 : W := mkw 0x044421fe954927d9 0x822210ff4aa493ec 0x7c0307ff9cc707f9 0xbe0183ffce6383fc

def z977 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xe3fffff0fc000001 0xf1fffff87e000000

def z978 : W := mkw 0x039ad50000514000 0x01cd6a800028a000 0xeffce7000379e001 0x77fe738001bcf000

def z979 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xb01ce7f49f39e598 0x580e73fa4f9cf2cc

def z980 : W := mkw 0x015600ce002c0140 0x00ab0067001600a0 0x87ff00f7007e01e1 0x43ff807b803f00f0

def z981 : W := mkw 0x00a8d4000290d000 0x00546a0001486800 0x83fce0000338e000 0x41fe7000019c7000

def z982 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfffcf8f8e3f9fe1f 0xfffe7c7c71fcff0f

def z983 : W := mkw 0x01570acf28000000 0x00ab856794000000 0xd3ff07ff1c000001 0xe9ff83ff8e000000

def z984 : W := mkw 0x015f6eefb8000000 0x00afb777dc000000 0xf3fffffffc000001 0xf9fffffffe000000

def z985 : W := mkw 0x8bbad50006f7d8ab 0x45dd6a80037bec55 0x8ffce00003fffffe 0x47fe700001ffffff

def z986 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xd3ffe7ff1c000001 0xe9fff3ff8e000000

def z987 : W := mkw 0x844420fdfd0827bf 0xc222107efe8413df 0x100000fffc0007fe 0x0800007ffe0003ff

def z988 : W := mkw 0x839bdf012c5348ab 0x41cdef809629a455 0xffffff0fffffffff 0xffffff87ffffffff

def z989 : W := mkw 0x944420fffd0825bb 0xca22107ffe8412dd 0x100000fffc0007fe 0x0800007ffe0003ff

def z990 : W := mkw 0x0bbbdf012af7d800 0x05ddef80957bec00 0xffffff0ffffffe1f 0xffffff87ffffff0f

def z991 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fffffffc0007e1 0xf9fffffffe0003f0

def z992 : W := mkw 0x01b2900002a49000 0x00d9480001524800 0x83fce0000338e000 0x41fe7000019c7000

def z993 : W := mkw 0x840c6574955b6dbb 0xc20632ba4aadb6dd 0xfc1cfffcffffffff 0xfe0e7ffe7fffffff

def z994 : W := mkw 0x00a8d50002d1d000 0x00546a800168e800 0xeffce7000379e001 0x77fe738001bcf000

def z995 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1ce7f49fffe7f9 0x7e0e73fa4ffff3fc

def z996 : W := mkw 0x135f4ecf38000000 0x09afa7679c000000 0x83ff07f71c000001 0x41ff83fb8e000000

def z997 : W := mkw 0x039ef46490000000 0x01cf7a3248000000 0xf3fce7f49c000001 0x79fe73fa4e000000

def z998 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fffffffc801a07 0xf9fffffffe400d03

def z999 : W := mkw 0x0bbad50002f7d800 0x05dd6a80017bec00 0xeffce70003fff801 0x77fe738001fffc00

def z1000 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff001ffff801 0xf7ffff800ffffc00

def z1001 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x87ffff0003fef801 0xc3ffff8001ff7c00

def z1002 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff0863fffa07 0xf7ffff8431fffd03

def z1003 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff0403fffd81 0xffffff8201fffec0

def z1004 : W := mkw 0x00c0b0b8c1002410 0x0060585c60801208 0xfbe0f8f8e381fe1e 0xfdf07c7c71c0ff0f

def z1005 : W := mkw 0x008cf46490000000 0x00467a3248000000 0xf3fcfff49c000001 0xf9fe7ffa4e000000

def z1006 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xfbfcf808e3b9fe1e 0xfdfe7c0471dcff0f

def z1007 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x8fff00fb03fe07e0 0xc7ff807d81ff03f0

def z1008 : W := mkw 0x015600ce00000000 0x00ab006700000000 0xf3ff07ff9c000001 0xf9ff83ffce000000

def z1009 : W := mkw 0x13dffeeff82c0140 0x09efff77fc1600a0 0xfffffffffcfe07e1 0xfffffffffe7f03f0

def z1010 : W := mkw 0x040c6574955967d9 0x820632ba4aacb3ec 0xfc1ce7f49f79e7f9 0x7e0e73fa4fbcf3fc

def z1011 : W := mkw 0x13dffeeff8002014 0x09efff77fc00100a 0xf3fffffffc00001f 0xf9fffffffe00000f

def z1012 : W := mkw 0x0bbbdf0202f7d840 0x05ddef81017bec20 0xefffff0303fff861 0xf7ffff8181fffc30

def z1013 : W := mkw 0x00c0b0a8c000b014 0x006058546000580a 0xfbe0f8f8e081fe1e 0xfdf07c7c7040ff0f

def z1014 : W := mkw 0x0bbbdf0006f7d889 0x05ddef80037bec44 0xffffff0f9ffffff9 0xffffff87cffffffc

def z1015 : W := mkw 0x004420fec1082754 0x0022107f608413aa 0x000000f000000000 0x0000007800000000

def z1016 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xec1ce7f41f79e181 0x760e73fa0fbcf0c0

def z1017 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0x83fce7f01c000000 0x41fe73f80e000000

def z1018 : W := mkw 0x01b2900002a49000 0x00d9480001524800 0xfffff80fe3ffffff 0xfffffc07f1ffffff

def z1019 : W := mkw 0x0bbad50002f5d000 0x05dd6a80017ae800 0xeffcff0003f9f801 0xf7fe7f8001fcfc00

def z1020 : W := mkw 0x8020011007c3bebf 0x4010008803e1df5f 0x080000000381fe1e 0x0400000001c0ff0f

def z1021 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff0f7ffffbe7 0xf7ffff87bffffdf3

def z1022 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0x8ffce00003fee000 0x47fe700001ff7000

def z1023 : W := mkw 0x040c647491186510 0x8206323a488c3288 0xa01ce7f09f38e000 0x500e73f84f9c7000

def z1024 : W := mkw 0x0bbbdf0006f7d889 0x05ddef80037bec44 0xffffff0cffffff9f 0xffffff867fffffcf

def z1025 : W := mkw 0x004420fcc1082714 0x0022107e6084138a 0x100000fce000079e 0x0800007e700003cf

def z1026 : W := mkw 0x0bbbde0002b6d800 0x05ddef00015b6c00 0xe3ffff0003bef801 0xf1ffff8001df7c00

def z1027 : W := mkw 0x0bbbdf0006f7d889 0x05ddef80037bec44 0xefffff041ffff981 0xf7ffff820ffffcc0

def z1028 : W := mkw 0x09b2910002f7d800 0x04d94880017bec00 0xeffff80003fff801 0xf7fffc0001fffc00

def z1029 : W := mkw 0x08a8d50002f7d800 0x04546a80017bec00 0xeffcff0003fff801 0xf7fe7f8001fffc00

def z1030 : W := mkw 0x015600de012c0540 0x00ab006f009602a0 0xdfff00ff037e05e1 0xefff807f81bf02f0

def z1031 : W := mkw 0x0004217485492599 0x000210ba42a492cc 0xfc1ce7f49f79e599 0x7e0e73fa4fbcf2cc

def z1032 : W := mkw 0x13dffeeff8080100 0x09efff77fc040080 0xf7fffffffc780181 0xfbfffffffe3c00c0

def z1033 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fcfff4fc000001 0x79fe7ffa7e000000

def z1034 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1fe7f49fffe599 0xfe0ff3fa4ffff2cc

def z1035 : W := mkw 0x0020011007c1b69d 0x0010008803e0db4e 0x0c00000003c1ff9e 0x0600000001e0ffcf

def z1036 : W := mkw 0x040c65749559679d 0x820632ba4aacb3ce 0xfc1ce7f49f79e79f 0x7e0e73fa4fbcf3cf

def z1037 : W := mkw 0x0420011007fd6599 0x8210008803feb2cc 0x0c00000003ffe598 0x0600000001fff2cc

def z1038 : W := mkw 0x0420011007d9f79d 0x8210008803ecfbce 0x0c0000000379e598 0x0600000001bcf2cc

def z1039 : W := mkw 0x13f39a8b6aa49244 0x09f9cd45b5524922 0x03e3180b60861a66 0x81f18c05b0430d33

def z1040 : W := mkw 0x1bbbdf013af7d800 0x0dddef809d7bec00 0xefffff001ffff801 0xf7ffff800ffffc00

def z1041 : W := mkw 0x13dffeeed0000000 0x09efff7768000000 0xf3fffff49c000001 0xf9fffffa4e000000

def z1042 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff04fffffd9f 0xffffff827ffffecf

def z1043 : W := mkw 0x0420011007d1f69d 0x8210008803e8fb4e 0x080000000381fe1e 0x0400000001c0ff0f

def z1044 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xcbfce00003b8e000 0xe5fe700001dc7000

def z1045 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1cfffcff79e599 0xfe0e7ffe7fbcf2cc

def z1046 : W := mkw 0x01b2900002a49000 0x00d9480001524800 0xcfffe00003fee001 0xe7fff00001ff7000

def z1047 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xcffce0000378e001 0x67fe700001bc7000

def z1048 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xf3e0f8f8e301f81e 0xf9f07c7c7180fc0f

def z1049 : W := mkw 0x13d3baabe8000000 0x09e9dd55f4000000 0xf3e3fffffc000001 0xf9f1fffffe000000

def z1050 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff00ffffffff 0xf7ffff807fffffff

def z1051 : W := mkw 0x8bbbde012ab6d822 0x45ddef00955b6c11 0x83fff80b63befa66 0xc1fffc05b1df7d33

def z1052 : W := mkw 0x040c647491186510 0x8206323a488c3288 0xf81ce7f49f39e419 0x7c0e73fa4f9cf20c

def z1053 : W := mkw 0x1bdffeeff810d000 0x0defff77fc086800 0xf3fffffffc00e001 0xf9fffffffe007000

def z1054 : W := mkw 0x840c6574955965bb 0xc20632ba4aacb2dd 0xfc1ce7f49f79e7ff 0x7e0e73fa4fbcf3ff

def z1055 : W := mkw 0x840c6574955b6dbb 0xc20632ba4aadb6dd 0xfc1ce7f49f7fe5f9 0x7e0e73fa4fbff2fc

def z1056 : W := mkw 0x12cdfeeff8000000 0x0966ff77fc000000 0xf3e0fffffc000000 0xf9f07ffffe000000

def z1057 : W := mkw 0x039bdf012c514089 0x01cdef809628a044 0xffffff0fff79e599 0xffffff87ffbcf2cc

def z1058 : W := mkw 0x03bbde0002a49000 0x01ddef0001524800 0xefffff0003fff801 0xf7ffff8001fffc00

def z1059 : W := mkw 0x1bdffeeff8260800 0x0defff77fc130400 0xf3fffffffc060001 0xf9fffffffe030000

def z1060 : W := mkw 0x00cdfeedf8000000 0x0066ff76fc000000 0xf3fffffffc000001 0xf9fffffffe000000

def z1061 : W := mkw 0x00e0b0b8c388b714 0x0070585c61c45b8a 0xffe0f8f8e3f9ff9e 0xfff07c7c71fcffcf

def z1062 : W := mkw 0x0bbad50002f7d800 0x05dd6a80017bec00 0xcfffe00003fff801 0xe7fff00001fffc00

def z1063 : W := mkw 0x000c646490104000 0x0006323248082000 0xf01ce7f49f38e001 0x780e73fa4f9c7000

def z1064 : W := mkw 0x00a8d4000290d000 0x00546a0001486800 0xebfcf80003b9f800 0xf5fe7c0001dcfc00

def z1065 : W := mkw 0x0bbbdf012af7d800 0x05ddef80957bec00 0xffffff0fffffffe1 0xffffff87fffffff0

def z1066 : W := mkw 0x0000010004410089 0x0000008002208044 0x7c031f0ffcc71fff 0xbe018f87fe638fff

def z1067 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff0703fff9e1 0xf7ffff8381fffcf0

def z1068 : W := mkw 0x015e64ee90000000 0x00af327748000000 0xf3fce7f49c000001 0x79fe73fa4e000000

def z1069 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xeffff80003fff801 0xf7fffc0001fffc00

def z1070 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xec1ce7f09f79e019 0x760e73f84fbcf00c

def z1071 : W := mkw 0x144420fed1082510 0x8a22107f68841288 0x000000f000000000 0x0000007800000000

def z1072 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xffff00ff83ff07f9 0xffff807fc1ff83fc

def z1073 : W := mkw 0x0bbad50002f7d800 0x05dd6a80017bec00 0x87fce000037ee000 0x43fe700001bf7000

def z1074 : W := mkw 0x93dffeeff8020822 0x49efff77fc010411 0xf3fffffffc001807 0xf9fffffffe000c03

def z1075 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xefffff07fffff9ff 0xf7ffff83fffffcff

def z1076 : W := mkw 0x0b9bdf0000774800 0x05cdef80003ba400 0xefffff00037fe001 0xf7ffff8001bff000

def z1077 : W := mkw 0x0bbbde0002b4d000 0x05ddef00015a6800 0xebffff0003b9f801 0xf5ffff8001dcfc00

def z1078 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff0003fffe1f 0xf7ffff8001ffff0f

def z1079 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xffe0f8f8e3c7fffe 0xfff07c7c71e3ffff

def z1080 : W := mkw 0x13dfdecf38000000 0x09efef679c000000 0xf3ffffff1c000001 0xf9ffffff8e000000

def z1081 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0x8c1ce7f41f79e599 0x460e73fa0fbcf2cc

def z1082 : W := mkw 0x8bbbdf0006f7d8ab 0x45ddef80037bec55 0xefffff0003fff9e1 0xf7ffff8001fffcf0

def z1083 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0x83fce7000338e000 0x41fe7380019c7000

def z1084 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xcfff00f703fe01e1 0xe7ff807b81ff00f0

def z1085 : W := mkw 0x13dffeeff8240040 0x09efff77fc120020 0xf3fffffffc060061 0xf9fffffffe030030

def z1086 : W := mkw 0x84452bfdfd4b2fbf 0xc22295fefea597df 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z1087 : W := mkw 0x13dffeeff8000204 0x09efff77fc000102 0xf3fffffffc000207 0xf9fffffffe000103

def z1088 : W := mkw 0x011a450000514000 0x008d22800028a000 0xefffe7000379e001 0xf7fff38001bcf000

def z1089 : W := mkw 0x94452bfffd4b2dbb 0xca2295fffea596dd 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z1090 : W := mkw 0x01bad50002f5d000 0x00dd6a80017ae800 0xefffff0003fff801 0xf7ffff8001fffc00

def z1091 : W := mkw 0x11572aeff8000000 0x08ab9577fc000000 0xf3ff1ffffc000001 0xf9ff8ffffe000000

def z1092 : W := mkw 0x9689ff21fc5368bb 0xcb44ff90fe29b45d 0x2000ff00fc01f81e 0x10007f807e00fc0f

def z1093 : W := mkw 0x039bde0000104000 0x01cdef0000082000 0xe3ffff000338e001 0xf1ffff80019c7000

def z1094 : W := mkw 0x13dffeeff8009004 0x09efff77fc004802 0xf3fffffffc001807 0xf9fffffffe000c03

def z1095 : W := mkw 0x93dffeeff8020822 0x49efff77fc010411 0xfbfffffffc871e7f 0xfdfffffffe438f3f

def z1096 : W := mkw 0x8bbbdf012af7d822 0x45ddef80957bec11 0xffffff0f63ffffe7 0xffffff87b1fffff3

def z1097 : W := mkw 0x040c647491186510 0x8206323a488c3288 0xfc1ce7f49f78e581 0x7e0e73fa4fbc72c0

def z1098 : W := mkw 0x13def4eff8000000 0x09ef7a77fc000000 0xf3fce7fffc000001 0x79fe73fffe000000

def z1099 : W := mkw 0x039bdf0000534800 0x01cdef800029a400 0xefffff0003fff801 0xf7ffff8001fffc00

def z1100 : W := mkw 0x0c20011007ffff9d 0x8610008803ffffce 0x0c00000003ffff9e 0x0600000001ffffcf

def z1101 : W := mkw 0x8020011007ef0feb 0x4010008803f787f5 0x0c00000003fe07e0 0x0600000001ff03f0

def z1102 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0xdfffe00f03fee7e1 0xeffff00781ff73f0

def z1103 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0x83fce7f41c000001 0x41fe73fa0e000000

def z1104 : W := mkw 0x017600de03ac9740 0x00bb006f01d64ba0 0xdfff00ff03ffffe1 0xefff807f81fffff0

def z1105 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xa3fcff00ff39f81e 0x51fe7f807f9cfc0f

def z1106 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0xf3ffe7ff9c000001 0xf9fff3ffce000000

def z1107 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0xffffff0ffffff9e1 0xffffff87fffffcf0

def z1108 : W := mkw 0x044420fe91082750 0x8222107f488413a8 0x000000f000000000 0x0000007800000000

def z1109 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe3f8fbe387fe7e 0xfdf1fc7df1c3ff3f

def z1110 : W := mkw 0x044420fc95082799 0x8222107e4a8413cc 0x100000fc9c000798 0x0800007e4e0003cc

def z1111 : W := mkw 0x00e0b0b8c388b754 0x0070585c61c45baa 0xfbe0f8f8e381fffe 0xfdf07c7c71c0ffff

def z1112 : W := mkw 0x0bbbdf012af7d800 0x05ddef80957bec00 0xefffff0b63fff801 0xf7ffff85b1fffc00

def z1113 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xf81ce7f09f39e418 0x7c0e73f84f9cf20c

def z1114 : W := mkw 0x013a450006f54089 0x009d2280037aa044 0xffffe70f9fffe7f9 0xfffff387cffff3fc

def z1115 : W := mkw 0x8bbbdf012af7d822 0x45ddef80957bec11 0xffffff0ffffffa67 0xffffff87fffffd33

def z1116 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xa7ffff00037ff801 0x53ffff8001bffc00

def z1117 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xa3ffff0003bff800 0xd1ffff8001dffc00

def z1118 : W := mkw 0x0420011007fd67d9 0x8210008803feb3ec 0x0c0000000379e598 0x0600000001bcf2cc

def z1119 : W := mkw 0x0bb39a0002a69800 0x05d9cd0001534c00 0xeffff80003fff801 0xf7fffc0001fffc00

def z1120 : W := mkw 0x8bf39a8b2aa69a62 0x45f9cd4595534d31 0x03e3180b60861a66 0x81f18c05b0430d33

def z1121 : W := mkw 0x017600de03acb754 0x00bb006f01d65baa 0xffff18ffe3ffffff 0xffff8c7ff1ffffff

def z1122 : W := mkw 0x13dffeeff8104000 0x09efff77fc082000 0xf3ffffffff38e001 0xf9ffffffff9c7000

def z1123 : W := mkw 0x093a450002f7d800 0x049d2280017bec00 0xefffe70003fff801 0xf7fff38001fffc00

def z1124 : W := mkw 0x14452bfffd492599 0x8a2295fffea492cc 0x7c031ffffc410599 0xbe018ffffe2082cc

def z1125 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xa3fffffbfc000000 0xd1fffffdfe000000

def z1126 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xa3e0f8f8e381fa1e 0xd1f07c7c71c0fd0f

def z1127 : W := mkw 0x0bbbdf012ef7d889 0x05ddef80977bec44 0xffffff0ffffffd99 0xffffff87fffffecc

def z1128 : W := mkw 0x1bf39a8b6aa69a04 0x0df9cd45b5534d02 0x03e3180b60861a06 0x81f18c05b0430d03

def z1129 : W := mkw 0x0420011007d96799 0x8210008803ecb3cc 0x0c00000003f9e798 0x0600000001fcf3cc

def z1130 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xffff18ff03ff1fe1 0xffff8c7f81ff8ff0

def z1131 : W := mkw 0x13dffeeff8000240 0x09efff77fc000120 0xf3fffffffc000261 0xf9fffffffe000130

def z1132 : W := mkw 0x13def4eed0000000 0x09ef7a7768000000 0xa3fce7f09c000000 0x51fe73f84e000000

def z1133 : W := mkw 0x80452bffed4b2fff 0x402295fff6a597ff 0x7c031ffffcc71fff 0xbe018ffffe638fff

def z1134 : W := mkw 0x00c8f4a8d0000000 0x00647a5468000000 0xf3e0fff8fc000000 0xf9f07ffc7e000000

def z1135 : W := mkw 0x017600de03ac9744 0x00bb006f01d64ba2 0xdfff00ff03fe1fe7 0xefff807f81ff0ff3

def z1136 : W := mkw 0x0bbad50002f5d000 0x05dd6a80017ae800 0x8ffce0000379e000 0x47fe700001bcf000

def z1137 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfbfffffffc800601 0xfdfffffffe400300

def z1138 : W := mkw 0x004420fec1082754 0x0022107f608413aa 0x7c0318ffe0c71fff 0xbe018c7ff0638fff

def z1139 : W := mkw 0x0c20011007ffffd9 0x8610008803ffffec 0x0c00000003fffff8 0x0600000001fffffc

def z1140 : W := mkw 0x0bbad50002f5d000 0x05dd6a80017ae800 0xefffe70003ffe001 0xf7fff38001fff000

def z1141 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xb3e0f8f8e301fe1e 0x59f07c7c7180ff0f

def z1142 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xe3ffff000339f801 0xf1ffff80019cfc00

def z1143 : W := mkw 0x0bbbde0002b6d800 0x05ddef00015b6c00 0x83ffe000033ee000 0x41fff000019f7000

def z1144 : W := mkw 0x0bbbde0002b6d800 0x05ddef00015b6c00 0x83fcf8000338f800 0x41fe7c00019c7c00

def z1145 : W := mkw 0x0bbbdf0006f7d889 0x05ddef80037bec44 0xefffff009ffff819 0xf7ffff804ffffc0c

def z1146 : W := mkw 0x813b4f012ef748ab 0x409da780977ba455 0xffffff0fffffffff 0xffffff87ffffffff

def z1147 : W := mkw 0x8bbbdf0006f7d8ab 0x45ddef80037bec55 0xffffff0f03ffffff 0xffffff8781ffffff

def z1148 : W := mkw 0x9b1f4f473c7748ab 0x4d8fa7a39e3ba455 0x041f07071c7e01e1 0x020f83838e3f00f0

def z1149 : W := mkw 0x0bbbdf0002f7da04 0x05ddef80017bed02 0xefffff0003fffa07 0xf7ffff8001fffd03

def z1150 : W := mkw 0x00a0900002809000 0x0050480001404800 0xeffcf80003f9f801 0xf7fe7c0001fcfc00

def z1151 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0xfc1f1f0fffff1fff 0xfe0f8f87ffff8fff

def z1152 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xefffff0003ffffe1 0xf7ffff8001fffff0

def z1153 : W := mkw 0x8020011007c30eab 0x4010008803e18755 0x0c00000003c71ffe 0x0600000001e38fff

def z1154 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0xdfff00ff03ff1fff 0xefff807f81ff8fff

def z1155 : W := mkw 0x0bbbde0002b4d000 0x05ddef00015a6800 0x83fff8000338e000 0xc1fffc00019c7000

def z1156 : W := mkw 0x1bbbdf016af7d800 0x0dddef80b57bec00 0xefffff0063fff801 0xf7ffff8031fffc00

def z1157 : W := mkw 0x040c657491596510 0x820632ba48acb288 0xfc1ce7f49f79e001 0x7e0e73fa4fbcf000

def z1158 : W := mkw 0x004420fec1082754 0x0022107f608413aa 0x100000f8e000061e 0x0800007c7000030f

def z1159 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff08e3fff801 0xffffff8471fffc00

def z1160 : W := mkw 0x03dffeee90000000 0x01efff7748000000 0xf3ffffff9c000001 0xf9ffffffce000000

def z1161 : W := mkw 0x0bbbdf0002f7da40 0x05ddef80017bed20 0xefffff0003fffa61 0xf7ffff8001fffd30

def z1162 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0x14031f0ffcc61fff 0x8a018f87fe630fff

def z1163 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xfbfffffffc811801 0xfdfffffffe408c00

def z1164 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xf3fffffffc01181f 0xf9fffffffe008c0f

def z1165 : W := mkw 0x044420fcd5082599 0x8222107e6a8412cc 0x100000fcfc000598 0x0800007e7e0002cc

def z1166 : W := mkw 0x040c657495596599 0x820632ba4aacb2cc 0xfc1ce7ff9f79e7f9 0x7e0e73ffcfbcf3fc

def z1167 : W := mkw 0x1bdffeeff8344000 0x0defff77fc1a2000 0xf3fffffffc380001 0xf9fffffffe1c0000

def z1168 : W := mkw 0x1bf39a8b6aa69a40 0x0df9cd45b5534d20 0x03e3180b60861a60 0x81f18c05b0430d30

def z1169 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff0f03fff801 0xffffff8781fffc00

def z1170 : W := mkw 0x144420fff9082510 0x8a22107ffc841288 0x100000fffc000000 0x0800007ffe000000

def z1171 : W := mkw 0x13dffeeff8000000 0x09efff77fc000000 0xb3fcfffffc000000 0x59fe7ffffe000000

def z1172 : W := mkw 0x044421fcd549279d 0x822210fe6aa493ce 0x7c001ffcfcc11f9f 0xbe000ffe7e608fcf

def z1173 : W := mkw 0x844420ffbd0827fb 0xc222107fde8413fd 0x100000fffc0007fe 0x0800007ffe0003ff

def z1174 : W := mkw 0x93dffeeff8020822 0x49efff77fc010411 0xfffffffffcc61fe7 0xfffffffffe630ff3

def z1175 : W := mkw 0x8bbbdf012ef7d8ab 0x45ddef80977bec55 0x87ffe7071f7ee1e1 0x43fff3838fbf70f0

def z1176 : W := mkw 0x013a450002f54000 0x009d2280017aa000 0xeffce7000379e001 0x77fe738001bcf000

def z1177 : W := mkw 0x93dffeeff8000022 0x49efff77fc000011 0xf3fffffffc000267 0xf9fffffffe000133

def z1178 : W := mkw 0x0028450002d14000 0x001422800168a000 0xeffce70003f9e001 0xf7fe738001fcf000

def z1179 : W := mkw 0x00e0b0b8c380b614 0x0070585c61c05b0a 0xfbe0fffcff81fe1f 0xfdf07ffe7fc0ff0f

def z1180 : W := mkw 0x0bbbdf0002f7d800 0x05ddef80017bec00 0xffffff0fe3ffffff 0xffffff87f1ffffff

def z1181 : W := mkw 0x017600ce02ac0340 0x00bb0067015601a0 0xd7ff00ff00fe03e1 0xebff807f807f01f0

def z1182 : W := mkw 0x115e64eff8000000 0x08af3277fc000000 0xf3ffe7fffc000001 0xf9fff3fffe000000

def z1183 : W := mkw 0x040c6576955965d9 0x820632bb4aacb2ec 0xfc1ce7f79f79e5f9 0x7e0e73fbcfbcf2fc

def z1184 : W := mkw 0x0420011007d9f599 0x8210008803ecfacc 0x0c00000003f9fd98 0x0600000001fcfecc

def z1185 : W := mkw 0x044420fed50827dd 0x8222107f6a8413ee 0x100000fffc0007fe 0x0800007ffe0003ff

def z1186 : W := mkw 0x80010b012c4308ab 0x4000858096218455 0xfc03ff0fffc7ffff 0xfe01ff87ffe3ffff

def z1187 : W := mkw 0x0bbad40002b4d000 0x05dd6a00015a6800 0x8bfce00003b9f800 0x45fe700001dcfc00

def z1188 : W := mkw 0x004420fe81082750 0x0022107f408413a8 0x100000ff800007f8 0x0800007fc00003fc

def z1189 : W := mkw 0x017600de03ac0740 0x00bb006f01d603a0 0x97ff00ff037e07e1 0x4bff807f81bf03f0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z7,z4,z8,z6]),(0,[z9,z0,z2,z3,z4,z8,z6]),(0,[z10,z0,z2,z11,z4,z8,z6]),(0,[z0,z2,z3,z4,z12,z8,z6]),(0,[z13,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z14])],[(0,[z0,z2,z15,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z6,z17]),(0,[z0,z2,z3,z4,z8,z18,z6])],[(0,[z0,z19,z2,z3,z20,z8,z6]),(0,[z0,z2,z21,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z22,z6]),(0,[z23,z24,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z25]),(0,[z0,z2,z3,z26,z4,z8,z6])],[(0,[z27,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z28]),(0,[z0,z2,z3,z4,z29,z8,z6]),(0,[z0,z2,z3,z29,z8,z6,z16]),(0,[z0,z2,z3,z4,z30,z6,z31])],[(0,[z0,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z32,z6,z31]),(0,[z0,z2,z3,z4,z8,z33,z6]),(1,[z0,z34,z2,z3,z4,z6]),(0,[z0,z2,z3,z35,z4,z8,z6]),(0,[z0,z2,z36,z4,z37,z8,z6]),(0,[z0,z2,z38,z36,z4,z8,z6]),(0,[z0,z2,z3,z39,z40,z8,z6]),(0,[z0,z2,z3,z41,z20,z8,z6])],[(0,[z0,z42,z2,z3,z4,z8,z6]),(0,[z43,z0,z2,z3,z4,z8,z6]),(0,[z44,z0,z45,z2,z3,z4,z6]),(1,[z0,z46,z2,z3,z4,z6]),(0,[z0,z2,z47,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z48,z8,z6])],[(0,[z0,z2,z49,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z50,z6,z31]),(0,[z51,z0,z2,z4,z37,z8,z6]),(0,[z0,z2,z52,z3,z4,z40,z6])],[(0,[z0,z2,z3,z4,z53,z8,z6]),(0,[z51,z0,z2,z3,z36,z8,z6]),(0,[z54,z0,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z56]),(0,[z2,z3,z4,z8,z57,z6,z58]),(0,[z0,z2,z3,z59,z4,z8,z6]),(0,[z60,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z61,z4,z8,z6])],[(0,[z0,z2,z3,z4,z62,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z63]),(0,[z0,z2,z3,z4,z8,z6,z64]),(0,[z65,z0,z2,z3,z4,z8,z6])],[(0,[z66,z0,z2,z3,z4,z30,z6]),(0,[z67,z0,z2,z3,z4,z8,z6]),(1,[z0,z45,z3,z4,z68,z6]),(0,[z69,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z70,z6]),(1,[z0,z2,z15,z4,z71,z6]),(0,[z0,z2,z3,z4,z8,z6,z72])],[(1,[z0,z2,z3,z4,z53,z6]),(0,[z0,z2,z3,z4,z73,z8,z6]),(0,[z23,z74,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z75,z76]),(0,[z44,z0,z2,z3,z4,z6,z31]),(0,[z0,z2,z3,z20,z8,z6,z77])],[(0,[z0,z45,z2,z3,z4,z32,z6]),(0,[z0,z2,z3,z4,z78,z8,z6])],[(0,[z79,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z80,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z81]),(1,[z82,z0,z3,z83,z8,z6]),(1,[z0,z2,z3,z4,z84,z6]),(0,[z0,z2,z3,z85,z4,z8,z6]),(0,[z86,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z87,z3,z4,z8,z6]),(0,[z2,z88,z3,z89,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z90,z6]),(0,[z0,z2,z3,z4,z91,z8,z6]),(0,[z92,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z93]),(0,[z0,z2,z3,z20,z40,z8,z6]),(0,[z0,z94,z2,z3,z4,z8,z6]),(0,[z95,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z96,z3,z4,z8,z6]),(0,[z97,z0,z2,z3,z4,z8,z6])]],
   [[(0,[z98,z0,z2,z3,z4,z99,z6]),(0,[z100,z0,z2,z3,z4,z101,z6]),(0,[z0,z2,z3,z4,z8,z6,z102]),(1,[z0,z2,z3,z103,z8,z6])],[(0,[z65,z104,z0,z2,z3,z4,z6]),(0,[z105,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z106,z6]),(0,[z107,z0,z2,z3,z4,z8,z6]),(0,[z108,z0,z2,z3,z4,z8,z6])],[(0,[z109,z0,z2,z3,z73,z8,z6]),(0,[z0,z2,z3,z4,z8,z68,z6]),(0,[z0,z2,z52,z38,z3,z8,z6]),(0,[z0,z2,z3,z4,z110,z6,z111])],[(0,[z112,z0,z2,z3,z4,z8,z6])],[(0,[z0,z55,z3,z4,z50,z8,z6]),(0,[z0,z2,z3,z4,z113,z8,z6]),(0,[z114,z0,z2,z3,z4,z8,z6]),(0,[z0,z115,z2,z3,z4,z8,z76]),(0,[z0,z2,z52,z3,z8,z116,z6])],[(0,[z117,z98,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z118]),(0,[z0,z2,z3,z4,z8,z6,z76]),(0,[z0,z2,z3,z103,z4,z8,z6])],[(0,[z117,z0,z55,z3,z4,z8,z6]),(0,[z119,z0,z2,z3,z89,z8,z6]),(0,[z120,z0,z2,z3,z4,z8,z6]),(1,[z109,z2,z3,z73,z8,z6]),(0,[z104,z0,z2,z3,z4,z32,z6]),(0,[z121,z0,z2,z3,z4,z8,z6])],[(0,[z122,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z123,z8,z6]),(0,[z0,z2,z3,z4,z8,z124,z6]),(0,[z0,z42,z2,z3,z20,z8,z6])]],
   [[(0,[z98,z2,z3,z4,z8,z6,z58]),(0,[z0,z2,z4,z8,z30,z6,z125])],[(0,[z0,z2,z3,z4,z8,z126,z6]),(0,[z0,z2,z127,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z128,z6])],[(0,[z121,z2,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z6]),(0,[z0,z2,z129,z3,z4,z8,z6])],[(0,[z130,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z131]),(0,[z132,z0,z2,z88,z4,z8,z6]),(0,[z0,z2,z3,z4,z133,z8,z6]),(0,[z134,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z135,z3,z4,z8,z6]),(0,[z65,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z136,z4,z8,z6])],[(0,[z137,z0,z2,z3,z4,z8,z6]),(0,[z138,z0,z2,z3,z4,z8,z6]),(0,[z67,z0,z2,z3,z20,z8,z6]),(1,[z0,z2,z3,z139,z8,z6]),(0,[z0,z140,z2,z3,z4,z8,z6]),(0,[z141,z0,z2,z3,z4,z8,z16])],[(0,[z0,z2,z142,z3,z4,z8,z6]),(0,[z0,z19,z2,z11,z4,z8,z6]),(0,[z23,z0,z2,z143,z4,z8,z6]),(0,[z0,z2,z3,z144,z4,z8,z6]),(1,[z0,z2,z145,z4,z8,z110]),(0,[z146,z0,z2,z3,z8,z6,z16])],[(0,[z0,z2,z3,z147,z4,z8,z6]),(0,[z0,z2,z3,z4,z148,z8,z6])],[(1,[z117,z55,z3,z4,z8,z6]),(0,[z149,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z150]),(0,[z0,z2,z151,z3,z4,z8,z6]),(0,[z0,z2,z3,z152,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z153,z6])]],
   [[(0,[z0,z1,z45,z3,z4,z8,z6]),(0,[z154,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z145,z3,z4,z8,z6]),(0,[z0,z2,z145,z4,z8,z110,z6])],[(0,[z0,z155,z2,z3,z4,z8,z6]),(0,[z156,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z157,z3,z4,z8,z6])],[(0,[z158,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z159,z8,z6]),(0,[z160,z0,z2,z3,z4,z8,z6]),(0,[z0,z161,z2,z3,z4,z8,z6]),(0,[z0,z2,z162,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z110,z6,z163]),(1,[z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z164,z3,z4,z8,z6])],[(0,[z165,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z166,z8,z6]),(0,[z0,z2,z3,z20,z8,z167,z6]),(0,[z0,z2,z3,z4,z101,z8,z6]),(0,[z168,z0,z2,z3,z4,z8,z6]),(0,[z67,z0,z45,z3,z4,z8,z6]),(0,[z0,z169,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z170,z8,z6]),(0,[z44,z0,z2,z3,z39,z4,z6]),(0,[z108,z0,z2,z3,z20,z8,z6])],[(0,[z0,z2,z3,z171,z8,z6,z16]),(0,[z0,z2,z3,z172,z4,z8,z6]),(0,[z0,z2,z3,z173,z8,z6,z16]),(0,[z0,z174,z2,z3,z4,z8,z6]),(0,[z67,z175,z2,z3,z4,z8,z6]),(0,[z0,z2,z176,z3,z8,z6,z16])],[(0,[z120,z0,z2,z38,z3,z8,z6]),(0,[z0,z45,z2,z3,z4,z50,z6]),(0,[z51,z44,z0,z2,z4,z8,z6]),(0,[z51,z0,z2,z52,z3,z8,z6]),(0,[z0,z2,z38,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z177,z8,z6]),(0,[z0,z2,z3,z4,z8,z178,z6]),(0,[z0,z2,z3,z20,z179,z8,z6]),(0,[z0,z2,z3,z180,z20,z8,z6]),(1,[z65,z0,z2,z3,z4,z31])],[(0,[z181,z0,z2,z3,z4,z8,z6]),(0,[z182,z0,z2,z3,z4,z8,z6]),(0,[z183,z0,z2,z3,z4,z8,z6])],[(0,[z132,z0,z2,z3,z8,z6,z16]),(0,[z0,z184,z2,z3,z4,z8,z6]),(0,[z23,z0,z115,z3,z4,z8,z6]),(0,[z0,z2,z38,z3,z37,z8,z6]),(0,[z0,z2,z3,z4,z185,z8,z6])]],
   [[(1,[z186,z0,z2,z3,z8,z6]),(0,[z120,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z187,z3,z4,z8,z6]),(0,[z121,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z4,z71,z8,z188,z6]),(0,[z189,z0,z2,z3,z190,z8,z6]),(0,[z0,z2,z191,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z192,z6])],[(0,[z193,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z194,z6]),(0,[z0,z2,z195,z3,z4,z37,z6]),(0,[z0,z2,z3,z4,z196,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z111]),(0,[z0,z2,z197,z3,z4,z8,z6])],[(0,[z0,z198,z2,z3,z4,z8,z6]),(0,[z199,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z200,z4,z8,z6]),(0,[z10,z0,z2,z3,z8,z6,z16]),(1,[z0,z2,z3,z201,z8,z6]),(0,[z202,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z203,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z204]),(0,[z0,z45,z2,z3,z4,z68,z6]),(0,[z0,z2,z3,z4,z8,z6,z205])],[(0,[z2,z55,z3,z4,z32,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z206]),(0,[z0,z2,z207,z3,z4,z8,z6])],[(0,[z120,z0,z2,z3,z171,z8,z6]),(0,[z67,z0,z2,z3,z4,z30,z6]),(0,[z0,z2,z3,z4,z8,z208,z6]),(0,[z0,z2,z3,z4,z8,z116,z6])],[(0,[z0,z209,z2,z3,z4,z8,z6]),(0,[z132,z0,z2,z89,z4,z8,z6]),(1,[z0,z2,z3,z8,z210,z6])],[(0,[z120,z109,z2,z3,z4,z8,z6]),(0,[z104,z0,z2,z3,z4,z50,z6]),(0,[z0,z211,z2,z3,z4,z8,z6]),(0,[z0,z2,z143,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z212,z4,z8,z6]),(0,[z213,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z214,z6]),(0,[z0,z215,z2,z3,z4,z8,z6]),(0,[z216,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z90,z6]),(0,[z217,z0,z2,z3,z4,z8,z6]),(0,[z0,z218,z2,z3,z4,z8,z6])],[(0,[z66,z0,z2,z3,z4,z32,z6]),(0,[z0,z2,z3,z36,z4,z8,z6]),(0,[z0,z2,z3,z4,z219,z8,z6])],[(1,[z220,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z37,z8,z6]),(0,[z0,z221,z2,z3,z4,z8,z6]),(0,[z0,z2,z145,z3,z20,z8,z6]),(0,[z0,z222,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z128,z8,z31])],[(0,[z0,z2,z3,z4,z223,z8,z6]),(0,[z0,z2,z3,z4,z8,z224,z6]),(0,[z0,z2,z3,z4,z225,z8,z6]),(0,[z0,z2,z3,z37,z8,z6,z16])],[(0,[z0,z2,z226,z3,z4,z8,z6]),(0,[z0,z2,z227,z3,z4,z8,z6]),(0,[z0,z2,z164,z3,z20,z8,z6])],[(0,[z104,z0,z2,z3,z4,z68,z6]),(1,[z44,z0,z2,z4,z188,z6]),(0,[z0,z2,z3,z20,z8,z110,z6])],[(0,[z228,z0,z2,z3,z4,z8,z6])],[(1,[z0,z2,z3,z229,z8,z6]),(0,[z109,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z73,z8,z6,z16]),(0,[z100,z0,z2,z3,z8,z6,z16]),(0,[z230,z0,z2,z3,z4,z8,z6]),(0,[z231,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z11,z145,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z232])]],
   [[(0,[z181,z0,z2,z3,z20,z8,z6]),(0,[z0,z233,z2,z3,z4,z8,z6]),(0,[z234,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z3,z4,z188,z6]),(0,[z0,z235,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z16,z236])],[(0,[z0,z2,z237,z3,z4,z8,z6]),(0,[z0,z2,z238,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z239,z8,z6]),(0,[z0,z2,z3,z4,z8,z240,z6])],[(0,[z0,z2,z3,z40,z8,z6,z16])],[(1,[z0,z2,z3,z241,z8,z6])],[(0,[z242,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z210,z6]),(0,[z243,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z244,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z245]),(0,[z0,z2,z3,z4,z8,z246,z6]),(0,[z199,z0,z2,z3,z20,z8,z6])],[(0,[z0,z2,z3,z20,z29,z8,z6]),(1,[z0,z2,z3,z247,z8,z6])],[(0,[z0,z2,z3,z248,z4,z8,z6]),(0,[z249,z0,z2,z3,z4,z8,z6]),(0,[z250,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z251])],[(0,[z252,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z253,z4,z8,z6]),(0,[z0,z2,z3,z8,z167,z6,z16]),(0,[z100,z0,z2,z200,z4,z8,z6]),(0,[z0,z2,z3,z254,z4,z8,z6]),(0,[z0,z2,z145,z4,z71,z8,z6])]],
   [[(0,[z98,z0,z2,z3,z4,z8,z6]),(0,[z44,z66,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z20,z32,z8,z6]),(1,[z0,z2,z3,z255,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z256]),(0,[z23,z0,z2,z3,z4,z8,z76])],[(0,[z0,z2,z3,z4,z8,z257,z6]),(0,[z0,z2,z3,z4,z8,z6,z258]),(0,[z0,z259,z2,z3,z4,z8,z6]),(0,[z0,z2,z260,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z261,z6]),(0,[z0,z11,z3,z173,z4,z8,z6]),(0,[z0,z2,z3,z4,z262,z8,z6]),(0,[z0,z2,z3,z4,z263,z8,z6]),(0,[z0,z2,z3,z8,z6,z16,z31])],[(0,[z98,z66,z2,z3,z4,z8,z6]),(0,[z264,z0,z2,z3,z4,z8,z6]),(0,[z0,z265,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z50,z8,z6]),(1,[z266,z0,z2,z4,z8,z6]),(0,[z0,z2,z3,z4,z128,z30,z6])],[(0,[z0,z2,z11,z3,z4,z8,z6]),(0,[z0,z2,z3,z267,z4,z8,z6]),(0,[z44,z0,z2,z36,z4,z8,z6]),(0,[z0,z2,z3,z36,z20,z8,z6]),(0,[z0,z2,z52,z15,z3,z4,z6])],[(0,[z268,z0,z2,z3,z4,z8,z6]),(0,[z65,z0,z45,z2,z3,z4,z6]),(0,[z51,z0,z2,z3,z40,z8,z6]),(0,[z0,z2,z52,z3,z4,z116,z6])],[(0,[z0,z2,z269,z3,z4,z8,z6]),(0,[z2,z55,z3,z4,z8,z6,z58]),(0,[z0,z2,z3,z270,z4,z8,z6]),(0,[z100,z0,z2,z3,z4,z90,z6]),(0,[z271,z0,z2,z3,z4,z8,z6]),(0,[z0,z45,z2,z15,z3,z4,z6]),(1,[z272,z2,z3,z4,z8,z6]),(1,[z24,z2,z3,z4,z8,z6]),(0,[z23,z0,z2,z3,z4,z8,z6]),(0,[z266,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z273,z4,z8,z6]),(0,[z274,z0,z2,z3,z4,z8,z6]),(0,[z65,z0,z2,z3,z4,z8,z30])],[(0,[z98,z0,z1,z3,z4,z8,z6]),(0,[z0,z19,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z275,z6])]],
   [[(1,[z0,z2,z3,z276,z4,z6])],[(0,[z0,z2,z3,z4,z277,z8,z6]),(0,[z51,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z38,z3,z36,z8,z6]),(1,[z0,z2,z3,z278,z8,z6]),(0,[z279,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z20,z8,z30,z6])],[(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z280,z8,z6]),(0,[z66,z0,z2,z3,z4,z50,z6]),(0,[z67,z0,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z281,z4,z8,z6]),(0,[z0,z233,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z282,z4,z8,z6]),(0,[z65,z0,z2,z3,z4,z6,z31])],[(0,[z0,z2,z3,z4,z283,z8,z6]),(0,[z120,z0,z233,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z284,z6]),(0,[z0,z2,z3,z285,z4,z8,z6]),(0,[z0,z2,z3,z4,z247,z8,z6]),(0,[z0,z2,z15,z3,z4,z71,z6]),(1,[z0,z2,z3,z4,z6,z111])],[(0,[z0,z2,z286,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z287,z6]),(0,[z288,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z39,z4,z8,z6]),(0,[z289,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z290,z8,z6])],[(0,[z291,z0,z2,z3,z4,z8,z6]),(0,[z0,z46,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z292,z4,z8,z6]),(0,[z0,z2,z293,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z294,z8,z6]),(0,[z0,z295,z2,z3,z4,z8,z6]),(0,[z65,z0,z2,z3,z103,z8,z6])],[(0,[z104,z0,z2,z15,z3,z4,z6]),(0,[z0,z2,z296,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z297]),(0,[z0,z2,z3,z39,z4,z40,z6])]],
   [[(1,[z181,z2,z89,z4,z8,z6]),(0,[z298,z0,z2,z3,z4,z8,z6]),(0,[z299,z0,z2,z3,z4,z8,z6]),(0,[z66,z0,z2,z3,z4,z68,z6]),(0,[z300,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z301,z4,z8,z6])],[(0,[z0,z2,z302,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z303]),(0,[z0,z304,z2,z3,z4,z8,z6])],[(0,[z98,z0,z2,z3,z20,z8,z6]),(0,[z51,z82,z0,z2,z3,z8,z6]),(1,[z189,z0,z2,z4,z8,z77])],[(0,[z0,z2,z3,z4,z8,z6,z305]),(0,[z0,z2,z306,z3,z4,z8,z6]),(0,[z307,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z308,z6]),(0,[z23,z0,z2,z3,z4,z309,z6]),(0,[z0,z2,z3,z20,z71,z8,z6])],[(0,[z100,z0,z2,z3,z255,z8,z6]),(0,[z0,z2,z3,z310,z4,z8,z6]),(0,[z0,z2,z311,z3,z4,z8,z6]),(1,[z0,z2,z3,z312,z8,z6])],[(0,[z0,z2,z3,z313,z4,z8,z6]),(0,[z0,z2,z3,z20,z4,z8,z6])],[(0,[z0,z314,z2,z3,z4,z8,z6]),(0,[z23,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z315,z4,z8,z6]),(1,[z0,z2,z3,z316,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z317,z8,z6]),(0,[z186,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z99,z6]),(0,[z0,z318,z2,z3,z4,z8,z6]),(0,[z319,z0,z2,z3,z4,z8,z6]),(0,[z320,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z8,z6,z321])],[(0,[z0,z2,z3,z89,z4,z8,z6]),(0,[z322,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z323]),(0,[z0,z2,z3,z4,z8,z324,z6]),(0,[z0,z2,z3,z20,z8,z6,z58]),(0,[z0,z2,z325,z3,z8,z6,z16])],[(0,[z0,z2,z3,z326,z4,z8,z6]),(0,[z0,z2,z52,z3,z8,z6,z16])],[(0,[z0,z2,z3,z32,z8,z6,z16]),(0,[z327,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z328,z8,z6]),(0,[z329,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z330])],[(0,[z0,z1,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z331,z4,z8,z6]),(0,[z0,z2,z11,z4,z8,z6,z77]),(0,[z0,z45,z2,z3,z8,z6,z16]),(0,[z0,z115,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z6,z75]),(0,[z0,z2,z3,z282,z20,z8,z6]),(1,[z0,z2,z332,z4,z8,z6])],[(0,[z0,z2,z55,z3,z20,z8,z6]),(0,[z0,z2,z3,z4,z333,z8,z6]),(0,[z0,z2,z200,z3,z4,z8,z6]),(0,[z0,z2,z3,z334,z4,z8,z6]),(0,[z141,z0,z2,z3,z8,z6,z16])],[(0,[z1,z2,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z335,z8,z6]),(0,[z10,z0,z19,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z336,z8,z6]),(0,[z0,z2,z3,z83,z8,z6,z16]),(0,[z0,z2,z3,z337,z4,z8,z6]),(0,[z0,z2,z3,z39,z20,z8,z6])],[(0,[z0,z2,z3,z4,z128,z167,z6]),(0,[z100,z0,z2,z3,z4,z8,z58]),(0,[z0,z2,z3,z338,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z339,z6]),(0,[z0,z2,z4,z8,z340,z116,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z62,z6]),(0,[z0,z2,z3,z4,z8,z341,z6]),(0,[z342,z0,z2,z3,z4,z8,z6]),(0,[z100,z121,z2,z3,z4,z8,z6]),(1,[z100,z2,z3,z4,z8,z58]),(0,[z0,z3,z83,z4,z29,z8,z6]),(0,[z0,z2,z3,z343,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z344])],[(0,[z0,z2,z3,z345,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z346,z6])],[(0,[z0,z2,z3,z4,z8,z347,z6]),(0,[z0,z2,z3,z4,z167,z6,z31]),(0,[z0,z2,z3,z20,z8,z57,z6]),(0,[z0,z2,z3,z4,z8,z6,z348]),(0,[z0,z233,z2,z3,z29,z8,z6]),(0,[z0,z2,z3,z4,z349,z8,z6]),(0,[z0,z2,z3,z4,z128,z8,z6])],[(0,[z0,z2,z3,z4,z8,z6,z350]),(0,[z0,z351,z2,z3,z173,z8,z6]),(0,[z0,z2,z3,z8,z6,z16,z297])],[(0,[z0,z55,z3,z4,z8,z6,z76]),(0,[z0,z2,z3,z4,z8,z6,z352]),(1,[z0,z260,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z353,z6]),(0,[z44,z0,z2,z3,z8,z6,z16])],[(0,[z0,z2,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z354,z8,z6]),(0,[z0,z45,z55,z3,z4,z8,z6]),(0,[z82,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z355]),(0,[z0,z2,z3,z71,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z356,z6]),(1,[z0,z2,z3,z20,z8,z246])],[(1,[z104,z2,z3,z4,z32,z6]),(0,[z104,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z357,z6]),(1,[z0,z2,z195,z3,z4,z6]),(0,[z0,z2,z3,z4,z8,z6,z321])],[(0,[z0,z2,z358,z3,z4,z8,z6]),(0,[z0,z1,z3,z4,z50,z8,z6]),(0,[z132,z2,z88,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z359,z6]),(0,[z0,z2,z3,z4,z8,z6,z360]),(0,[z0,z2,z15,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z116,z6]),(0,[z0,z2,z3,z20,z8,z6,z31]),(0,[z0,z2,z3,z4,z8,z6,z361])]],
   [[(1,[z0,z2,z3,z152,z8,z6]),(0,[z0,z2,z3,z8,z353,z6,z16]),(0,[z362,z0,z2,z3,z4,z8,z6]),(0,[z44,z0,z2,z15,z4,z8,z6]),(0,[z0,z2,z3,z20,z20,z8,z6])],[(0,[z0,z2,z3,z4,z8,z6,z363])],[(0,[z0,z2,z3,z364,z4,z8,z6]),(0,[z66,z0,z2,z15,z3,z4,z6]),(0,[z230,z0,z2,z3,z4,z6,z58]),(0,[z67,z0,z3,z4,z50,z8,z6]),(0,[z365,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z6,z16]),(0,[z320,z0,z2,z3,z20,z8,z6])],[(0,[z0,z2,z3,z89,z20,z8,z6]),(0,[z0,z2,z3,z366,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z367,z6]),(0,[z0,z368,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z369])],[(0,[z0,z2,z3,z4,z370,z8,z6]),(0,[z371,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z4,z8,z16])],[(0,[z372,z0,z2,z3,z4,z8,z6]),(0,[z121,z0,z2,z3,z8,z6,z16]),(0,[z67,z0,z2,z3,z4,z50,z6]),(0,[z0,z2,z3,z8,z110,z6,z16]),(0,[z0,z2,z3,z4,z8,z6,z373])],[(0,[z0,z2,z3,z4,z8,z374,z6]),(0,[z0,z2,z375,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z376,z6]),(0,[z0,z2,z3,z152,z8,z57,z6]),(0,[z0,z2,z3,z377,z4,z8,z6]),(0,[z0,z115,z2,z3,z20,z8,z6]),(0,[z189,z0,z2,z3,z139,z8,z6]),(0,[z0,z2,z3,z8,z6,z72,z16])],[(0,[z378,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z379,z3,z4,z8,z6]),(0,[z0,z2,z380,z3,z4,z8,z6]),(0,[z0,z45,z3,z4,z8,z68,z6]),(0,[z0,z2,z3,z334,z20,z8,z6])]],
   [[(0,[z381,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z382,z3,z4,z8,z6]),(1,[z141,z0,z2,z3,z8,z16]),(0,[z0,z2,z3,z20,z383,z8,z6]),(0,[z0,z384,z2,z3,z4,z8,z6])],[(0,[z385,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z386,z6])],[(0,[z387,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z201,z4,z8,z6])],[(0,[z117,z0,z2,z3,z4,z8,z6]),(0,[z67,z0,z2,z3,z4,z68,z6]),(0,[z0,z2,z195,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z16])],[(0,[z0,z2,z3,z4,z8,z388,z6]),(0,[z0,z2,z3,z4,z8,z389,z6]),(0,[z82,z0,z2,z38,z3,z8,z6]),(0,[z175,z0,z2,z3,z4,z8,z6]),(0,[z24,z0,z2,z3,z4,z8,z6]),(1,[z23,z0,z3,z4,z8,z76]),(0,[z189,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z390,z4,z8,z6])],[(0,[z0,z2,z3,z4,z391,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z392]),(0,[z0,z2,z3,z4,z32,z128,z6]),(0,[z393,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z394,z4,z8,z6]),(0,[z0,z2,z3,z395,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z396,z6]),(0,[z0,z2,z3,z397,z4,z8,z6]),(1,[z67,z0,z3,z4,z50,z6]),(0,[z0,z2,z3,z4,z8,z398,z6])],[(0,[z117,z2,z55,z3,z4,z8,z6]),(0,[z82,z0,z2,z3,z20,z8,z6]),(0,[z399,z0,z2,z3,z4,z8,z6]),(0,[z44,z67,z0,z2,z3,z4,z6]),(0,[z0,z2,z400,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z50,z128,z6]),(0,[z401,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z128,z30])]],
   [[(0,[z0,z2,z3,z4,z402,z8,z6]),(0,[z0,z2,z88,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z6,z403])],[(0,[z0,z2,z3,z4,z8,z99,z6]),(0,[z100,z0,z260,z3,z4,z8,z6]),(0,[z404,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z405,z3,z4,z8,z6]),(1,[z0,z2,z3,z8,z6,z406]),(0,[z0,z2,z15,z3,z20,z8,z6]),(0,[z0,z2,z3,z278,z8,z110,z6])],[(0,[z117,z0,z1,z3,z4,z8,z6]),(0,[z0,z2,z407,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z408,z8,z6]),(0,[z0,z2,z3,z4,z8,z409,z6]),(0,[z0,z2,z3,z4,z8,z188,z6])],[(0,[z181,z2,z3,z89,z4,z8,z6]),(0,[z0,z2,z410,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z411]),(0,[z189,z0,z2,z3,z4,z8,z110])],[(0,[z44,z0,z2,z3,z4,z128,z6]),(0,[z0,z2,z3,z8,z246,z6,z16])],[(0,[z0,z2,z3,z4,z8,z6,z75]),(0,[z0,z2,z3,z4,z8,z6,z412]),(0,[z0,z2,z3,z4,z8,z413,z6]),(0,[z0,z2,z191,z3,z20,z8,z6])],[(0,[z0,z2,z3,z4,z414,z8,z6]),(0,[z51,z0,z233,z2,z3,z8,z6]),(1,[z0,z2,z296,z3,z8,z6]),(0,[z0,z2,z145,z3,z4,z8,z110]),(0,[z0,z2,z3,z4,z8,z6,z415])],[(0,[z0,z2,z3,z416,z4,z8,z6]),(0,[z0,z2,z3,z229,z4,z8,z6]),(0,[z65,z66,z0,z2,z3,z4,z6]),(0,[z0,z417,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z418]),(0,[z0,z2,z4,z71,z8,z6,z77])]],
   [[(1,[z0,z2,z407,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z419,z6]),(0,[z0,z2,z3,z4,z8,z6,z420]),(0,[z0,z2,z3,z201,z8,z353,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z421,z2,z3,z4,z8,z6]),(0,[z422,z0,z2,z3,z4,z8,z6]),(0,[z66,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z6,z423]),(0,[z0,z2,z3,z424,z4,z8,z6]),(0,[z0,z2,z3,z4,z425,z8,z6])],[(1,[z0,z2,z3,z281,z8,z6]),(0,[z0,z2,z3,z4,z8,z426,z6]),(0,[z0,z2,z3,z4,z427,z8,z6]),(0,[z0,z2,z3,z4,z8,z428,z6])],[(0,[z429,z0,z2,z3,z4,z8,z6]),(1,[z0,z19,z11,z4,z8,z6]),(0,[z430,z0,z2,z3,z4,z8,z6]),(0,[z146,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z431,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z432]),(0,[z0,z2,z3,z4,z8,z6,z433]),(0,[z0,z2,z3,z4,z434,z8,z6]),(0,[z0,z2,z3,z128,z8,z6,z16])],[(0,[z117,z0,z2,z3,z20,z8,z6]),(1,[z0,z151,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z435,z6])],[(0,[z98,z1,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z436,z8,z6]),(0,[z104,z0,z151,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z437,z58]),(0,[z0,z2,z3,z4,z8,z438,z6]),(0,[z0,z2,z38,z3,z40,z8,z6])],[(1,[z66,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z8,z439,z6]),(0,[z23,z0,z2,z3,z4,z84,z6]),(0,[z0,z2,z3,z4,z8,z6,z406]),(0,[z0,z2,z3,z8,z6,z16,z16])]],
   [[(1,[z0,z2,z3,z4,z8,z6]),(0,[z0,z440,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z73,z8,z6]),(0,[z100,z0,z2,z3,z4,z8,z57]),(0,[z0,z2,z3,z4,z8,z441,z6]),(0,[z0,z2,z3,z4,z128,z68,z6]),(0,[z0,z2,z3,z36,z8,z6,z16])],[(0,[z442,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z443,z6]),(0,[z444,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z171,z4,z8,z6]),(0,[z0,z2,z3,z173,z4,z8,z6]),(0,[z0,z233,z2,z38,z3,z8,z6]),(0,[z0,z445,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z446,z6]),(0,[z0,z2,z176,z3,z4,z8,z6]),(0,[z0,z447,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z448,z6]),(0,[z120,z0,z2,z3,z73,z8,z6]),(0,[z104,z2,z3,z4,z32,z8,z6]),(0,[z0,z2,z38,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z449]),(0,[z0,z2,z3,z4,z450,z8,z6])],[(0,[z451,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z452,z6]),(0,[z44,z0,z2,z4,z8,z188,z6])],[(0,[z0,z453,z2,z3,z4,z8,z6]),(0,[z132,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z454,z6]),(0,[z0,z2,z3,z4,z8,z455,z6]),(0,[z0,z456,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z457,z8,z6]),(0,[z0,z2,z3,z4,z8,z340,z6]),(0,[z0,z2,z3,z39,z4,z116,z6])],[(0,[z0,z2,z458,z3,z4,z8,z6]),(0,[z141,z0,z2,z3,z4,z8,z246])],[(0,[z0,z2,z3,z4,z8,z6,z459]),(0,[z82,z0,z2,z3,z29,z8,z6]),(0,[z0,z2,z3,z4,z460,z8,z6]),(0,[z0,z2,z3,z20,z8,z68,z6]),(0,[z461,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z16,z411]),(0,[z0,z462,z2,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z8,z463,z6]),(0,[z10,z0,z2,z3,z4,z8,z6]),(0,[z464,z0,z2,z3,z4,z8,z6]),(0,[z465,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z466,z6])],[(0,[z0,z2,z3,z4,z8,z467,z6]),(0,[z468,z0,z2,z3,z4,z8,z6]),(1,[z74,z2,z3,z4,z8,z6]),(0,[z189,z0,z2,z3,z4,z8,z77]),(0,[z469,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z470])],[(0,[z0,z2,z3,z4,z8,z6,z471]),(0,[z0,z2,z3,z276,z89,z4,z6]),(0,[z0,z2,z3,z20,z8,z6,z76]),(0,[z472,z0,z2,z3,z4,z8,z6])],[(0,[z473,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z89,z4,z8,z6,z77])],[(0,[z2,z3,z171,z4,z73,z8,z6]),(0,[z0,z2,z474,z3,z4,z8,z6]),(0,[z0,z2,z145,z3,z4,z8,z77])],[(0,[z181,z132,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z139,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z475,z6])],[(0,[z119,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z476,z4,z8,z6])],[(0,[z0,z2,z3,z477,z4,z8,z6]),(0,[z67,z0,z2,z3,z4,z32,z6]),(1,[z230,z0,z2,z3,z4,z6]),(1,[z0,z2,z3,z4,z309,z6]),(0,[z478,z0,z2,z3,z4,z8,z6]),(0,[z479,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z6,z6])]],
   [[(0,[z0,z2,z11,z3,z20,z8,z6]),(0,[z480,z0,z2,z3,z4,z8,z6])],[(0,[z0,z481,z2,z3,z4,z8,z6])],[(0,[z0,z3,z4,z50,z8,z68,z6]),(0,[z0,z2,z3,z278,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z482,z6]),(0,[z0,z115,z3,z4,z8,z353,z6]),(0,[z44,z0,z2,z3,z4,z188,z6]),(0,[z442,z0,z2,z3,z20,z8,z6])],[(0,[z120,z2,z3,z171,z4,z8,z6]),(0,[z0,z2,z3,z171,z20,z8,z6]),(0,[z0,z2,z3,z173,z20,z8,z6]),(0,[z0,z2,z3,z20,z128,z8,z6])],[(0,[z109,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z483,z6]),(0,[z100,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z4,z6,z437]),(0,[z0,z2,z3,z8,z57,z6,z16]),(0,[z0,z2,z3,z8,z68,z6,z16]),(0,[z0,z484,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z485])],[(0,[z486,z0,z2,z3,z4,z8,z6]),(0,[z51,z0,z2,z3,z20,z8,z6]),(1,[z0,z2,z38,z36,z8,z6])],[(0,[z0,z2,z3,z4,z8,z487,z6]),(0,[z0,z2,z3,z4,z8,z488,z6]),(0,[z132,z0,z2,z3,z20,z8,z6]),(0,[z0,z489,z2,z3,z4,z8,z6]),(0,[z0,z2,z490,z3,z4,z8,z6]),(0,[z0,z2,z491,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z128,z8,z30])]],
   [[(0,[z492,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z493,z3,z4,z8,z6]),(1,[z0,z2,z4,z8,z340,z6])],[(0,[z0,z1,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z276,z4,z8,z6]),(0,[z0,z2,z494,z3,z4,z8,z6]),(0,[z0,z2,z495,z3,z4,z8,z6]),(0,[z51,z0,z2,z38,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z496,z6])],[(0,[z0,z2,z55,z3,z8,z6,z16]),(0,[z497,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z5,z6]),(1,[z175,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z498,z8,z6]),(0,[z0,z2,z3,z4,z499,z8,z6]),(1,[z0,z2,z143,z4,z8,z6]),(0,[z0,z2,z3,z39,z8,z6,z16]),(0,[z65,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z6,z500])],[(0,[z109,z2,z3,z4,z73,z8,z6]),(0,[z67,z0,z2,z3,z8,z6,z16]),(0,[z0,z501,z2,z3,z4,z8,z6])],[(0,[z502,z0,z2,z3,z4,z8,z6]),(0,[z220,z0,z2,z3,z89,z4,z6]),(0,[z503,z0,z2,z3,z4,z8,z6]),(0,[z10,z0,z2,z173,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z167,z6]),(0,[z82,z0,z233,z3,z4,z8,z6]),(0,[z504,z0,z2,z3,z4,z8,z6]),(0,[z505,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z506,z8,z6]),(0,[z0,z2,z507,z3,z4,z8,z6]),(0,[z0,z2,z3,z508,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z509])],[(0,[z0,z2,z3,z510,z4,z8,z6]),(0,[z0,z2,z3,z511,z4,z8,z6]),(0,[z0,z2,z512,z3,z4,z8,z6])]],
   [[(0,[z513,z0,z2,z3,z4,z8,z6]),(0,[z51,z109,z0,z2,z3,z8,z6]),(0,[z0,z514,z2,z3,z4,z8,z6]),(0,[z0,z2,z515,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z516,z6]),(0,[z0,z2,z15,z3,z4,z6,z31]),(0,[z0,z2,z52,z3,z39,z8,z6]),(0,[z0,z94,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z517,z6]),(0,[z0,z2,z3,z4,z316,z8,z6])],[(0,[z0,z2,z3,z4,z8,z8,z6]),(0,[z0,z2,z518,z3,z4,z8,z6]),(0,[z0,z2,z36,z4,z71,z8,z6]),(0,[z0,z2,z3,z4,z8,z519,z6])],[(0,[z0,z2,z3,z520,z4,z8,z6])],[(0,[z51,z0,z2,z4,z71,z8,z6]),(0,[z0,z2,z3,z4,z452,z37,z6]),(0,[z0,z2,z3,z521,z4,z8,z6])],[(0,[z522,z0,z2,z3,z4,z8,z6]),(0,[z109,z0,z2,z38,z3,z8,z6]),(0,[z0,z2,z523,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z6,z524]),(0,[z0,z2,z3,z20,z8,z6,z16])],[(0,[z0,z525,z2,z3,z4,z8,z6]),(0,[z44,z0,z2,z3,z4,z71,z6])],[(0,[z279,z0,z2,z3,z4,z8,z6]),(0,[z109,z0,z2,z3,z20,z8,z6]),(0,[z526,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z527,z4,z6]),(0,[z0,z2,z3,z20,z37,z8,z6])]],
   [[(0,[z120,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z528,z8,z6])],[(0,[z23,z0,z2,z529,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z530])],[(0,[z0,z2,z3,z531,z4,z8,z6]),(0,[z0,z2,z3,z4,z452,z8,z6]),(0,[z329,z0,z2,z3,z8,z6,z16])],[(0,[z532,z0,z2,z3,z4,z8,z6]),(0,[z533,z0,z2,z3,z4,z8,z6]),(0,[z0,z534,z2,z3,z4,z8,z6]),(0,[z0,z115,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z6,z535])],[(0,[z181,z0,z2,z88,z4,z8,z6]),(0,[z109,z0,z2,z3,z171,z8,z6]),(0,[z0,z2,z536,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z537,z6]),(0,[z538,z0,z2,z3,z4,z8,z6])],[(0,[z539,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z540,z6]),(0,[z0,z2,z3,z4,z8,z541,z6]),(0,[z10,z0,z3,z173,z4,z8,z6]),(0,[z0,z2,z3,z4,z542,z8,z6]),(0,[z0,z2,z3,z4,z8,z543,z6])],[(0,[z0,z2,z544,z3,z4,z8,z6]),(1,[z119,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z545,z6]),(0,[z65,z67,z0,z2,z3,z4,z6])],[(0,[z0,z2,z3,z546,z4,z8,z6]),(0,[z0,z1,z3,z4,z8,z6,z76]),(0,[z0,z2,z3,z4,z8,z547,z6]),(0,[z0,z2,z3,z4,z548,z8,z6]),(0,[z0,z2,z3,z4,z8,z549,z6]),(0,[z0,z2,z3,z4,z8,z550,z6]),(0,[z0,z2,z551,z3,z4,z8,z6]),(0,[z0,z2,z552,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z3,z4,z8,z6]),(0,[z100,z2,z3,z4,z8,z6,z58]),(0,[z0,z2,z553,z3,z4,z8,z6]),(0,[z0,z554,z2,z3,z4,z8,z6])],[(0,[z555,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z556,z6]),(0,[z0,z2,z3,z557,z4,z8,z6]),(0,[z558,z0,z2,z3,z4,z8,z6]),(0,[z0,z46,z2,z3,z4,z6,z76]),(0,[z0,z2,z3,z4,z8,z6,z559]),(0,[z0,z2,z3,z20,z8,z246,z6])],[(0,[z560,z0,z2,z3,z4,z8,z6]),(0,[z561,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z145,z3,z8,z6,z16]),(0,[z266,z0,z2,z4,z8,z116,z6])],[(0,[z562,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z563]),(0,[z0,z2,z3,z4,z564,z8,z6]),(0,[z0,z2,z3,z48,z8,z6,z16]),(0,[z65,z0,z2,z3,z4,z128,z6])],[(0,[z565,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z566,z4,z8,z6]),(0,[z0,z2,z567,z3,z4,z8,z6]),(0,[z0,z568,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z569])],[(0,[z570,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z571,z6]),(0,[z0,z2,z3,z241,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z6,z437]),(0,[z121,z0,z2,z3,z4,z8,z57]),(0,[z572,z0,z2,z3,z4,z8,z6]),(0,[z44,z0,z2,z145,z4,z8,z6])],[(0,[z573,z0,z2,z3,z4,z8,z6]),(0,[z0,z45,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z574,z8,z6]),(0,[z0,z351,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z353,z6,z406]),(0,[z0,z2,z3,z4,z528,z110,z6]),(0,[z0,z2,z325,z3,z4,z8,z6]),(1,[z0,z2,z4,z8,z6,z125])]],
   [[(0,[z98,z121,z2,z3,z4,z8,z6]),(0,[z181,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z68,z6,z31]),(0,[z0,z2,z3,z4,z8,z575,z6]),(0,[z0,z2,z15,z3,z39,z4,z6]),(0,[z0,z2,z52,z3,z4,z8,z6])],[(0,[z0,z2,z145,z89,z4,z8,z6]),(1,[z0,z2,z3,z8,z6,z576]),(0,[z0,z2,z577,z3,z4,z8,z6]),(0,[z0,z272,z2,z3,z4,z8,z6]),(0,[z23,z0,z2,z3,z4,z8,z353]),(0,[z0,z2,z3,z4,z8,z578,z6]),(0,[z279,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z4,z8,z579,z6])],[(0,[z0,z2,z3,z4,z8,z6,z580]),(0,[z0,z19,z2,z173,z4,z8,z6]),(0,[z0,z34,z2,z3,z173,z4,z6]),(0,[z0,z45,z2,z3,z4,z8,z6])],[(0,[z98,z0,z2,z3,z4,z53,z6]),(0,[z0,z2,z3,z4,z32,z8,z6]),(0,[z141,z0,z2,z3,z4,z8,z6])],[(0,[z82,z109,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z83,z4,z8,z6]),(0,[z82,z0,z3,z83,z4,z8,z6]),(0,[z0,z581,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z8,z582,z6]),(0,[z0,z2,z583,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z50,z8,z6])],[(0,[z0,z2,z3,z584,z4,z8,z6])],[(0,[z181,z0,z2,z89,z4,z8,z6]),(0,[z67,z272,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z585,z4,z8,z6])]],
   [[(1,[z132,z2,z88,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z586]),(0,[z0,z2,z3,z4,z587,z8,z6])],[(0,[z0,z588,z2,z3,z4,z8,z6]),(0,[z51,z120,z0,z2,z3,z8,z6]),(0,[z104,z0,z2,z3,z4,z167,z6]),(0,[z0,z2,z15,z4,z71,z8,z6]),(0,[z589,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z290,z8,z6])],[(0,[z117,z0,z2,z3,z8,z6,z16]),(1,[z0,z2,z3,z133,z8,z6]),(0,[z590,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z591,z8,z6]),(0,[z0,z74,z2,z3,z4,z8,z6]),(0,[z44,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z592,z8,z6]),(0,[z0,z2,z4,z8,z110,z6,z77]),(0,[z0,z2,z3,z312,z8,z30,z6])],[(0,[z0,z2,z3,z4,z8,z6,z593]),(0,[z0,z2,z3,z594,z4,z8,z6])],[(0,[z0,z2,z3,z595,z4,z8,z6]),(0,[z104,z0,z2,z3,z4,z8,z6]),(0,[z66,z2,z3,z4,z8,z167,z6]),(0,[z0,z2,z596,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z30,z6])],[(0,[z597,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z255,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z16,z559]),(0,[z0,z2,z3,z598,z4,z8,z6])],[(0,[z104,z66,z2,z3,z4,z8,z6]),(0,[z0,z19,z11,z3,z4,z8,z6]),(0,[z0,z2,z3,z599,z4,z8,z6]),(0,[z189,z0,z2,z145,z4,z8,z6])],[(0,[z0,z2,z3,z4,z600,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z576]),(1,[z51,z0,z2,z37,z8,z6]),(1,[z0,z2,z3,z4,z528,z6])]],
   [[(0,[z0,z2,z3,z4,z601,z8,z6]),(0,[z0,z2,z3,z180,z4,z8,z6]),(0,[z602,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z603,z8,z6]),(0,[z604,z0,z2,z3,z4,z8,z6]),(0,[z67,z0,z2,z15,z3,z4,z6]),(0,[z0,z2,z3,z50,z8,z6,z16]),(0,[z605,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z606,z6]),(0,[z0,z2,z3,z4,z8,z607,z6])],[(0,[z0,z2,z3,z4,z608,z8,z6]),(0,[z609,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z77]),(0,[z0,z2,z3,z8,z6,z500,z16])],[(0,[z0,z2,z610,z3,z4,z8,z6]),(0,[z0,z2,z88,z145,z4,z8,z6]),(0,[z109,z0,z233,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z611,z8,z6]),(0,[z44,z104,z0,z2,z3,z4,z6]),(0,[z0,z233,z2,z3,z8,z6,z16]),(0,[z0,z2,z52,z3,z20,z8,z6]),(0,[z234,z0,z2,z3,z8,z6,z16])],[(0,[z2,z3,z4,z32,z8,z167,z6]),(0,[z0,z612,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z188,z6,z16]),(0,[z0,z2,z3,z613,z4,z8,z6]),(0,[z0,z2,z3,z8,z30,z6,z321])],[(0,[z0,z2,z3,z4,z8,z614,z6]),(0,[z0,z45,z2,z3,z20,z8,z6]),(0,[z44,z0,z2,z52,z3,z4,z6]),(0,[z0,z2,z3,z4,z40,z8,z6])],[(0,[z186,z0,z2,z55,z3,z8,z6]),(0,[z0,z2,z3,z615,z4,z8,z6]),(0,[z82,z0,z2,z3,z83,z8,z6]),(0,[z141,z0,z2,z3,z20,z8,z6])],[(0,[z616,z0,z2,z3,z4,z8,z6]),(0,[z0,z233,z3,z4,z29,z8,z6]),(0,[z0,z2,z3,z83,z20,z8,z6]),(1,[z0,z2,z3,z190,z8,z6]),(0,[z617,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z116,z6,z16]),(0,[z0,z618,z2,z3,z4,z8,z6]),(0,[z619,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z620,z8,z6]),(0,[z0,z2,z3,z4,z71,z8,z6]),(0,[z0,z2,z3,z4,z8,z621,z6]),(0,[z622,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z8,z6,z163]),(0,[z0,z2,z3,z312,z4,z8,z6])]],
   [[(0,[z121,z0,z2,z3,z4,z8,z58]),(0,[z0,z2,z3,z4,z8,z623,z6]),(0,[z0,z115,z2,z3,z4,z8,z353]),(0,[z624,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z569,z16]),(0,[z65,z0,z2,z3,z316,z8,z6])],[(0,[z0,z2,z3,z4,z8,z625,z6]),(0,[z0,z2,z3,z4,z4,z8,z6]),(1,[z120,z2,z3,z171,z8,z6]),(1,[z0,z2,z584,z4,z8,z6]),(0,[z0,z2,z3,z4,z626,z8,z6]),(0,[z65,z0,z2,z3,z4,z8,z31])],[(0,[z627,z0,z2,z3,z4,z8,z6]),(0,[z98,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z628,z3,z4,z8,z6]),(0,[z629,z0,z2,z3,z4,z8,z6]),(0,[z0,z630,z2,z3,z4,z8,z6]),(0,[z189,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z631,z8,z6])],[(0,[z632,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z633,z3,z4,z8,z6]),(0,[z634,z0,z2,z3,z4,z8,z6]),(0,[z120,z82,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z58]),(0,[z0,z2,z3,z527,z4,z8,z6]),(0,[z635,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z636,z8,z6]),(0,[z44,z0,z2,z3,z20,z8,z6])],[(0,[z637,z0,z2,z3,z4,z8,z6]),(0,[z638,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z639,z8,z6]),(0,[z640,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z11,z3,z8,z6,z16]),(1,[z0,z2,z3,z20,z8,z6]),(0,[z641,z0,z2,z3,z4,z8,z6])],[(0,[z0,z2,z88,z3,z4,z8,z6]),(0,[z104,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z4,z642,z8,z6]),(0,[z0,z2,z3,z20,z4,z8,z246])],[(0,[z100,z0,z2,z3,z133,z8,z6]),(0,[z643,z0,z2,z3,z4,z8,z6]),(0,[z23,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z20,z349,z8,z6])]],
   [[(0,[z0,z2,z644,z3,z4,z8,z6]),(0,[z0,z2,z645,z3,z4,z8,z6]),(0,[z0,z2,z3,z646,z4,z8,z6]),(0,[z0,z2,z38,z3,z20,z8,z6]),(0,[z0,z2,z3,z8,z6,z647,z16]),(0,[z0,z2,z3,z8,z30,z6,z16])],[(1,[z0,z2,z3,z4,z62,z6]),(0,[z0,z2,z3,z4,z8,z6,z236]),(0,[z0,z2,z3,z4,z648,z8,z6]),(0,[z0,z2,z3,z529,z4,z8,z6])],[(0,[z649,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z650,z8,z6]),(0,[z651,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z517,z6])],[(0,[z652,z0,z2,z3,z4,z8,z6]),(0,[z653,z0,z2,z3,z4,z8,z6]),(0,[z98,z0,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z654]),(0,[z655,z0,z2,z3,z4,z8,z6]),(0,[z51,z0,z2,z3,z8,z6,z16]),(0,[z44,z0,z2,z4,z8,z6,z77])],[(0,[z0,z2,z3,z656,z4,z8,z6]),(0,[z66,z0,z2,z3,z4,z167,z6]),(1,[z0,z161,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z190,z8,z6])],[(0,[z0,z2,z3,z4,z8,z57,z6]),(0,[z10,z0,z2,z3,z20,z8,z6]),(0,[z0,z45,z2,z3,z4,z30,z6]),(0,[z51,z0,z2,z3,z37,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z163]),(0,[z0,z2,z332,z3,z4,z8,z6])],[(0,[z657,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z658,z4,z8,z6]),(0,[z659,z0,z2,z3,z4,z8,z6]),(1,[z0,z115,z3,z4,z8,z353]),(0,[z0,z2,z660,z3,z4,z8,z6])],[(0,[z66,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z661,z6]),(0,[z0,z2,z3,z4,z8,z353,z6])]],
   [[(0,[z0,z2,z3,z8,z6,z58,z16]),(0,[z0,z2,z3,z4,z662,z8,z6]),(1,[z0,z2,z52,z3,z116,z6])],[(0,[z0,z1,z115,z3,z4,z8,z6]),(0,[z0,z2,z173,z4,z8,z6,z77]),(0,[z0,z2,z3,z4,z663,z8,z6]),(0,[z664,z0,z2,z3,z4,z8,z6])],[(0,[z665,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z210,z188,z6]),(0,[z0,z2,z3,z4,z8,z6,z666]),(0,[z0,z2,z3,z4,z8,z6,z31])],[(0,[z66,z2,z55,z3,z4,z8,z6]),(0,[z0,z233,z2,z3,z83,z8,z6]),(0,[z0,z2,z3,z4,z8,z84,z6]),(0,[z0,z2,z3,z4,z179,z8,z6])],[(0,[z189,z0,z2,z3,z20,z8,z6])],[(0,[z0,z2,z3,z4,z8,z6,z667])],[(0,[z0,z2,z3,z4,z8,z6,z668]),(0,[z100,z0,z2,z584,z4,z8,z6]),(0,[z0,z2,z3,z281,z173,z8,z6]),(0,[z669,z0,z2,z3,z4,z8,z6])],[(0,[z104,z0,z2,z3,z4,z30,z6]),(0,[z670,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z671,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z672]),(0,[z0,z2,z3,z4,z8,z6,z125])]],
   [[(0,[z0,z2,z88,z3,z20,z8,z6]),(0,[z0,z19,z2,z3,z4,z8,z6]),(0,[z0,z34,z2,z3,z4,z8,z6]),(0,[z673,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z674,z6]),(0,[z675,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z296,z3,z8,z188,z6]),(0,[z0,z2,z3,z4,z8,z676,z6])],[(0,[z677,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z527,z173,z4,z6])],[(0,[z100,z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z678]),(0,[z0,z2,z145,z173,z4,z8,z6]),(0,[z0,z2,z3,z679,z4,z8,z6]),(0,[z0,z3,z4,z8,z353,z6,z76]),(0,[z0,z2,z3,z41,z4,z8,z6]),(0,[z680,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z681,z6]),(0,[z319,z0,z2,z3,z8,z6,z16])],[(0,[z0,z2,z3,z89,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z682,z6]),(1,[z121,z2,z3,z4,z8,z57]),(1,[z0,z233,z3,z29,z8,z6]),(0,[z189,z0,z2,z4,z8,z6,z77]),(1,[z0,z2,z3,z20,z8,z16]),(0,[z0,z2,z3,z4,z383,z8,z6]),(0,[z0,z2,z683,z3,z4,z8,z6])],[(1,[z0,z2,z529,z4,z8,z6]),(0,[z0,z2,z3,z4,z309,z8,z6]),(0,[z0,z2,z3,z40,z8,z116,z6])],[(0,[z23,z0,z3,z4,z8,z6,z76]),(0,[z0,z684,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z77,z16]),(0,[z0,z2,z3,z4,z8,z685,z6])],[(0,[z0,z686,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z687])],[(0,[z0,z2,z407,z55,z3,z8,z6]),(0,[z220,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z688,z8,z6]),(0,[z0,z2,z88,z4,z8,z6,z77]),(0,[z0,z2,z3,z4,z689,z8,z6]),(0,[z0,z2,z690,z3,z4,z8,z6]),(0,[z121,z2,z3,z4,z8,z57,z6]),(1,[z0,z351,z2,z3,z8,z6]),(0,[z691,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z188,z6]),(0,[z0,z2,z3,z692,z4,z8,z6])]],
   [[(0,[z23,z0,z2,z3,z241,z8,z6])],[(0,[z0,z2,z3,z4,z693,z8,z6]),(0,[z66,z0,z2,z3,z20,z8,z6]),(0,[z100,z0,z161,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z57,z6,z576]),(0,[z694,z0,z2,z3,z4,z8,z6]),(1,[z0,z2,z3,z39,z40,z6]),(0,[z0,z2,z332,z4,z8,z30,z6])],[(1,[z10,z0,z173,z4,z8,z6]),(0,[z23,z0,z2,z3,z247,z8,z6]),(0,[z0,z2,z3,z8,z6,z76,z16]),(0,[z695,z0,z2,z3,z4,z8,z6]),(0,[z696,z0,z2,z3,z4,z8,z6])],[(1,[z0,z2,z3,z4,z101,z6]),(0,[z0,z2,z3,z4,z697,z8,z6]),(0,[z0,z2,z3,z4,z698,z8,z6]),(0,[z0,z2,z3,z4,z8,z110,z6])],[(0,[z699,z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z700,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z6,z647])],[(1,[z0,z417,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z701,z8,z6])],[(0,[z104,z0,z417,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z702,z8,z6]),(0,[z0,z2,z3,z703,z4,z8,z6])],[(0,[z0,z115,z55,z3,z4,z8,z6]),(0,[z98,z2,z3,z4,z32,z8,z6]),(0,[z0,z2,z3,z229,z89,z8,z6]),(0,[z0,z2,z3,z704,z4,z8,z6]),(0,[z705,z0,z2,z3,z4,z8,z6]),(0,[z82,z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z8,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z584,z4,z8,z6]),(0,[z120,z2,z3,z171,z8,z6]),(0,[z0,z260,z3,z255,z8,z6]),(0,[z0,z45,z3,z20,z68,z6]),(0,[z0,z2,z3,z139,z8,z6]),(0,[z0,z2,z3,z8,z6,z707])],[(0,[z0,z2,z3,z20,z53,z6]),(0,[z0,z2,z3,z4,z708,z6]),(0,[z0,z2,z709,z3,z8,z6]),(0,[z0,z3,z710,z4,z8,z6]),(0,[z0,z2,z145,z4,z8,z110]),(0,[z0,z2,z20,z8,z340,z6])],[(0,[z0,z2,z3,z711,z4,z6]),(0,[z712,z0,z2,z3,z4,z6]),(0,[z51,z0,z2,z390,z8,z6]),(0,[z0,z2,z15,z4,z713,z6])],[(0,[z117,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z714,z8,z6]),(0,[z0,z151,z3,z8,z6,z16]),(0,[z100,z230,z2,z3,z4,z58]),(0,[z0,z2,z15,z424,z4,z6]),(0,[z0,z2,z3,z20,z84,z6]),(0,[z0,z2,z3,z282,z290,z6])],[(0,[z0,z2,z3,z715,z8,z6]),(0,[z95,z2,z3,z4,z167,z6]),(0,[z0,z417,z3,z4,z30,z6])],[(0,[z716,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z717,z8,z6]),(0,[z44,z0,z2,z210,z188,z6])],[(0,[z718,z2,z3,z4,z8,z6]),(0,[z719,z2,z3,z4,z8,z6]),(0,[z0,z2,z720,z4,z8,z6]),(0,[z272,z2,z3,z8,z6,z16])],[(0,[z0,z2,z4,z8,z110,z721]),(0,[z0,z2,z52,z340,z116,z6]),(0,[z0,z2,z3,z20,z722,z6])]],
   [[(0,[z0,z2,z3,z4,z62,z6]),(0,[z0,z2,z3,z723,z8,z6]),(0,[z724,z0,z3,z4,z8,z6]),(0,[z104,z0,z2,z332,z4,z6]),(0,[z0,z2,z3,z20,z528,z6])],[(0,[z181,z220,z2,z89,z4,z6]),(0,[z0,z2,z164,z36,z8,z6])],[(0,[z117,z725,z3,z4,z8,z6]),(0,[z657,z2,z3,z4,z8,z58]),(0,[z0,z2,z3,z4,z726,z6]),(0,[z0,z2,z727,z4,z8,z6]),(0,[z0,z161,z3,z133,z8,z6]),(0,[z0,z2,z3,z4,z728,z6]),(0,[z0,z2,z729,z4,z8,z6])],[(0,[z0,z161,z3,z4,z8,z6]),(0,[z0,z2,z3,z730,z8,z6]),(0,[z121,z260,z3,z4,z8,z6]),(0,[z10,z0,z710,z4,z8,z6]),(0,[z82,z0,z3,z338,z8,z6]),(0,[z0,z45,z3,z4,z460,z6]),(0,[z0,z3,z4,z731,z68,z6]),(0,[z0,z46,z2,z3,z20,z6]),(0,[z0,z2,z3,z20,z8,z578])],[(0,[z2,z55,z3,z4,z62,z6]),(0,[z0,z2,z732,z3,z8,z6]),(0,[z0,z2,z733,z4,z8,z6]),(0,[z0,z2,z3,z4,z734,z6]),(0,[z0,z2,z3,z8,z6,z735]),(0,[z736,z2,z3,z4,z8,z6]),(0,[z0,z115,z3,z8,z353,z406]),(0,[z0,z2,z737,z4,z8,z6])],[(0,[z0,z738,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z467]),(0,[z0,z115,z3,z4,z8,z353]),(0,[z23,z0,z3,z247,z8,z76]),(0,[z0,z739,z2,z3,z8,z6]),(0,[z0,z2,z3,z528,z6,z16]),(0,[z0,z2,z332,z312,z8,z6])],[(0,[z0,z2,z200,z4,z8,z6]),(0,[z0,z2,z3,z201,z8,z6]),(0,[z0,z2,z740,z3,z4,z6]),(0,[z0,z2,z4,z128,z30,z125])],[(0,[z0,z2,z3,z741,z8,z6]),(0,[z0,z742,z3,z4,z8,z6]),(0,[z0,z2,z3,z743,z8,z6]),(0,[z0,z2,z3,z4,z744,z6]),(0,[z0,z2,z3,z4,z745,z6]),(0,[z74,z2,z3,z8,z6,z16]),(0,[z0,z2,z52,z3,z208,z6]),(0,[z0,z2,z4,z8,z346,z77]),(0,[z0,z2,z4,z71,z6,z666]),(0,[z0,z2,z52,z3,z116,z6])]],
   [[(0,[z0,z2,z3,z4,z746,z6]),(1,[z51,z0,z2,z195,z6])],[(0,[z0,z2,z3,z276,z229,z6]),(0,[z0,z2,z3,z4,z747,z6]),(0,[z0,z2,z3,z8,z178,z16]),(0,[z2,z3,z8,z6,z748,z16]),(0,[z234,z0,z3,z8,z6,z647])],[(0,[z749,z0,z2,z4,z8,z6]),(0,[z44,z0,z2,z594,z4,z6]),(0,[z0,z2,z584,z20,z8,z6]),(0,[z0,z2,z3,z4,z750,z6]),(0,[z0,z2,z52,z3,z751,z6])],[(0,[z0,z2,z3,z752,z8,z6]),(0,[z0,z753,z3,z4,z8,z6]),(0,[z175,z2,z3,z4,z32,z6]),(0,[z2,z3,z4,z8,z754,z58]),(0,[z2,z3,z4,z8,z6,z755]),(0,[z0,z2,z145,z20,z8,z110])],[(0,[z0,z2,z3,z4,z90,z6])],[(0,[z117,z55,z3,z20,z8,z6]),(0,[z23,z74,z3,z4,z8,z76]),(0,[z0,z2,z3,z756,z8,z6])],[(0,[z220,z0,z2,z3,z4,z6]),(0,[z220,z0,z2,z4,z6,z77]),(0,[z0,z2,z3,z8,z6,z757]),(0,[z0,z2,z3,z758,z8,z6])],[(0,[z0,z2,z3,z4,z759,z6]),(0,[z0,z2,z3,z4,z6,z760]),(0,[z230,z0,z2,z3,z6,z16]),(0,[z23,z0,z3,z4,z8,z761]),(0,[z0,z2,z3,z762,z8,z6])]],
   [[(0,[z763,z0,z2,z3,z4,z6]),(0,[z0,z764,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z765,z6]),(0,[z766,z2,z3,z4,z8,z6])],[(0,[z0,z161,z584,z4,z8,z6])],[(0,[z0,z2,z3,z20,z62,z6]),(0,[z109,z612,z2,z3,z8,z6]),(0,[z120,z2,z3,z8,z6,z72]),(0,[z121,z2,z3,z4,z8,z57]),(0,[z0,z233,z3,z29,z8,z6]),(0,[z0,z2,z529,z4,z84,z6]),(0,[z189,z0,z2,z4,z8,z721]),(1,[z0,z2,z3,z751,z6]),(0,[z0,z2,z3,z20,z8,z16])],[(0,[z13,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z229,z8,z6]),(0,[z82,z0,z3,z767,z8,z6])],[(0,[z0,z768,z3,z4,z8,z6])],[(0,[z652,z55,z3,z4,z8,z6]),(0,[z0,z161,z3,z20,z8,z6]),(0,[z0,z2,z3,z4,z8,z769])],[(0,[z0,z2,z3,z4,z770,z6]),(0,[z0,z2,z3,z771,z8,z6]),(0,[z0,z2,z38,z772,z8,z6])],[(0,[z773,z0,z2,z3,z4,z6]),(0,[z141,z0,z2,z3,z8,z774])]],
   [[(0,[z0,z2,z775,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z776]),(0,[z0,z2,z4,z8,z6,z777]),(0,[z100,z260,z3,z4,z8,z58]),(0,[z175,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z778,z8,z6]),(0,[z0,z2,z4,z8,z6,z779]),(0,[z0,z2,z20,z8,z6,z125])],[(0,[z0,z2,z3,z133,z101,z6]),(0,[z0,z2,z3,z247,z8,z6]),(0,[z0,z2,z143,z8,z6,z16]),(0,[z146,z0,z2,z37,z8,z6]),(0,[z266,z0,z2,z40,z8,z6]),(0,[z0,z2,z3,z4,z780,z31])],[],[(0,[z0,z2,z3,z4,z781,z6]),(0,[z0,z2,z3,z4,z466,z31])],[(0,[z0,z2,z3,z255,z8,z6]),(0,[z0,z782,z3,z4,z8,z6]),(0,[z10,z0,z34,z173,z4,z6]),(0,[z0,z2,z3,z4,z783,z6]),(0,[z0,z2,z3,z20,z8,z357]),(0,[z51,z0,z2,z195,z4,z6])],[(0,[z0,z2,z3,z8,z6,z784]),(0,[z74,z3,z4,z8,z6,z76])],[(0,[z0,z2,z3,z785,z8,z6]),(0,[z0,z2,z3,z20,z90,z6]),(0,[z0,z2,z3,z4,z8,z761]),(0,[z266,z0,z2,z4,z8,z6]),(0,[z0,z2,z8,z6,z125,z321])],[(0,[z0,z2,z3,z4,z786,z6]),(0,[z0,z2,z787,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z788]),(0,[z0,z2,z3,z789,z8,z6]),(0,[z0,z2,z3,z20,z8,z420]),(0,[z2,z3,z8,z6,z16,z790])]],
   [[(0,[z0,z2,z791,z4,z8,z6]),(0,[z0,z792,z3,z4,z8,z6]),(1,[z0,z3,z4,z731,z6]),(0,[z74,z2,z3,z241,z8,z6]),(0,[z793,z0,z2,z3,z4,z6]),(0,[z794,z2,z3,z4,z8,z6])],[(0,[z24,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z795]),(0,[z0,z2,z3,z527,z281,z6])],[(0,[z0,z2,z3,z796,z8,z6]),(0,[z0,z2,z3,z797,z8,z6]),(0,[z0,z2,z798,z4,z8,z6]),(0,[z0,z2,z3,z799,z8,z6]),(0,[z675,z0,z2,z3,z8,z16]),(0,[z74,z2,z3,z247,z8,z6]),(0,[z0,z2,z15,z4,z434,z6])],[(0,[z0,z417,z3,z4,z32,z6]),(0,[z0,z2,z3,z4,z128,z324]),(0,[z0,z34,z2,z3,z4,z6]),(0,[z0,z34,z2,z4,z6,z77]),(0,[z0,z2,z4,z8,z6,z800]),(0,[z65,z0,z2,z3,z20,z31])],[(0,[z0,z2,z3,z8,z471,z16]),(0,[z0,z2,z3,z276,z4,z6]),(0,[z121,z2,z3,z20,z8,z57]),(0,[z51,z0,z2,z452,z37,z6]),(0,[z0,z2,z3,z8,z16,z687])],[(0,[z0,z2,z3,z801,z4,z6]),(0,[z0,z2,z3,z4,z802,z6]),(0,[z442,z2,z3,z171,z8,z6]),(0,[z0,z2,z3,z4,z6,z780])],[(0,[z0,z45,z3,z4,z639,z6]),(0,[z0,z2,z3,z803,z8,z6]),(0,[z0,z2,z3,z804,z8,z6])],[(0,[z805,z0,z2,z3,z8,z6]),(0,[z806,z0,z2,z3,z8,z6]),(0,[z100,z2,z3,z4,z8,z754]),(0,[z0,z2,z3,z527,z6,z16]),(0,[z0,z2,z3,z4,z6,z111]),(0,[z0,z2,z3,z6,z807,z16]),(0,[z0,z2,z332,z4,z128,z30])]],
   [[(0,[z0,z2,z584,z4,z101,z6]),(0,[z808,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z247,z309,z6])],[(0,[z0,z2,z3,z8,z6,z809]),(0,[z0,z810,z3,z4,z8,z6]),(0,[z0,z2,z15,z4,z71,z6]),(0,[z44,z0,z2,z188,z6,z16]),(0,[z0,z2,z3,z40,z751,z6]),(0,[z811,z0,z2,z8,z6,z16])],[(0,[z0,z2,z3,z812,z8,z6]),(0,[z120,z2,z3,z813,z8,z6]),(0,[z0,z2,z3,z20,z8,z449])],[(0,[z0,z1,z46,z3,z4,z6]),(0,[z121,z2,z3,z8,z57,z576]),(0,[z0,z235,z11,z4,z8,z6]),(0,[z814,z2,z3,z4,z8,z6]),(0,[z0,z2,z8,z6,z125,z16])],[(0,[z0,z2,z3,z4,z815,z6]),(0,[z181,z2,z89,z4,z8,z6]),(0,[z0,z816,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z101,z6]),(0,[z0,z2,z8,z6,z16,z777]),(0,[z0,z2,z8,z6,z16,z779])],[(0,[z817,z0,z2,z3,z4,z6]),(0,[z186,z117,z55,z3,z8,z6]),(0,[z0,z2,z3,z8,z6,z818]),(0,[z0,z2,z819,z4,z8,z6]),(0,[z0,z2,z3,z4,z820,z6]),(0,[z821,z0,z2,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z822])],[(0,[z0,z2,z3,z8,z6,z823]),(0,[z0,z2,z3,z4,z6,z824]),(0,[z0,z2,z825,z4,z8,z6]),(0,[z0,z2,z3,z4,z751,z6]),(0,[z0,z2,z3,z39,z290,z6])],[(0,[z0,z2,z3,z4,z826,z6]),(0,[z266,z0,z2,z52,z3,z6])]],
   [[(0,[z220,z0,z2,z3,z20,z6]),(0,[z0,z2,z3,z827,z8,z6]),(0,[z0,z2,z3,z828,z8,z6]),(0,[z0,z2,z3,z4,z731,z6]),(0,[z24,z2,z3,z4,z309,z6])],[(0,[z0,z2,z829,z4,z8,z6]),(0,[z0,z2,z3,z4,z830,z6]),(1,[z0,z3,z767,z8,z6]),(0,[z0,z2,z3,z831,z8,z6]),(0,[z0,z2,z3,z6,z832,z16])],[(0,[z0,z2,z833,z4,z8,z6]),(0,[z381,z0,z2,z4,z8,z77]),(0,[z0,z2,z143,z241,z8,z6]),(0,[z0,z2,z3,z8,z6,z834])],[(0,[z0,z161,z3,z4,z101,z6])],[(0,[z0,z2,z3,z4,z99,z6]),(0,[z2,z3,z813,z4,z8,z6]),(0,[z835,z2,z3,z4,z8,z6]),(0,[z836,z2,z3,z4,z8,z6]),(0,[z0,z2,z143,z247,z8,z6]),(0,[z0,z2,z837,z3,z8,z6]),(0,[z0,z2,z3,z8,z6,z321])],[(0,[z119,z220,z0,z2,z3,z6]),(0,[z109,z2,z3,z73,z8,z6]),(0,[z0,z2,z3,z838,z8,z6]),(0,[z2,z3,z4,z8,z57,z754])],[(0,[z66,z2,z3,z4,z99,z6]),(0,[z0,z839,z3,z8,z6,z16])],[(0,[z840,z0,z2,z4,z8,z6]),(0,[z0,z2,z3,z6,z75,z16]),(0,[z0,z2,z36,z772,z8,z6])]],
   [[(0,[z0,z2,z3,z4,z841,z6]),(0,[z0,z2,z3,z4,z842,z6]),(0,[z0,z843,z3,z4,z8,z6]),(0,[z0,z2,z3,z20,z8,z582]),(0,[z104,z2,z3,z4,z6,z509]),(0,[z0,z2,z844,z4,z8,z6]),(0,[z0,z2,z3,z4,z6,z75]),(0,[z0,z2,z3,z845,z8,z6]),(0,[z0,z2,z332,z4,z8,z6]),(0,[z44,z0,z2,z4,z713,z6])],[(0,[z0,z2,z3,z846,z8,z6]),(0,[z0,z847,z3,z4,z8,z6]),(0,[z0,z2,z36,z8,z681,z6]),(0,[z44,z0,z2,z4,z339,z6]),(0,[z0,z2,z3,z20,z6,z111]),(0,[z65,z0,z2,z3,z316,z31])],[(0,[z0,z2,z3,z848,z8,z6]),(0,[z849,z2,z3,z4,z8,z6]),(0,[z10,z0,z281,z173,z8,z6]),(0,[z850,z2,z3,z4,z8,z6]),(0,[z272,z45,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z851]),(0,[z0,z46,z2,z3,z6,z16]),(0,[z0,z2,z3,z20,z8,z475]),(0,[z0,z2,z3,z6,z16,z852])],[(0,[z0,z2,z3,z853,z8,z6]),(0,[z0,z2,z3,z4,z854,z6]),(0,[z0,z2,z38,z679,z8,z6]),(0,[z855,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z20,z71,z6])],[(0,[z0,z856,z2,z3,z8,z6]),(0,[z0,z417,z3,z4,z50,z6]),(0,[z100,z2,z3,z4,z8,z58]),(0,[z0,z19,z11,z8,z6,z16]),(0,[z24,z2,z143,z4,z8,z6])],[(0,[z0,z2,z3,z857,z8,z6]),(0,[z0,z2,z3,z4,z6,z858]),(0,[z0,z2,z3,z8,z6,z859]),(0,[z10,z0,z527,z173,z4,z6]),(0,[z67,z0,z3,z613,z4,z6])],[(0,[z0,z2,z3,z860,z8,z6]),(0,[z181,z2,z89,z20,z8,z6]),(0,[z0,z2,z3,z861,z8,z6]),(0,[z132,z2,z88,z8,z6,z16]),(0,[z0,z2,z862,z4,z8,z6]),(0,[z0,z2,z3,z863,z8,z6]),(0,[z0,z2,z3,z864,z8,z6]),(0,[z0,z2,z3,z8,z124,z16])],[(0,[z0,z2,z3,z4,z865,z6]),(0,[z104,z151,z3,z4,z32,z6]),(0,[z0,z2,z3,z866,z8,z6]),(0,[z0,z2,z52,z3,z517,z6]),(0,[z867,z0,z2,z8,z6,z16])]],
   [[(0,[z0,z2,z3,z868,z4,z8]),(0,[z181,z119,z2,z89,z8,z6]),(0,[z0,z2,z145,z4,z528,z110])],[(0,[z0,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z4,z869,z6]),(0,[z0,z2,z3,z870,z8,z6]),(0,[z0,z2,z3,z767,z8,z6]),(0,[z0,z2,z3,z8,z751,z6]),(0,[z0,z2,z3,z8,z871,z6])],[(0,[z0,z2,z3,z4,z872,z6]),(0,[z627,z2,z3,z4,z32,z6]),(0,[z0,z417,z3,z4,z68,z6])],[(0,[z0,z2,z873,z4,z8,z6]),(0,[z0,z2,z874,z3,z8,z6]),(0,[z0,z875,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z876]),(0,[z0,z2,z3,z877,z8,z6])],[(0,[z0,z2,z3,z152,z8,z6]),(0,[z175,z2,z15,z3,z4,z6]),(0,[z65,z0,z2,z3,z4,z31])],[(0,[z0,z2,z878,z3,z4,z6]),(0,[z0,z2,z3,z4,z879,z6]),(0,[z0,z3,z4,z8,z6,z880]),(0,[z132,z2,z881,z4,z8,z6]),(0,[z0,z2,z3,z148,z8,z16]),(0,[z0,z34,z2,z3,z20,z6]),(0,[z74,z2,z143,z4,z8,z6]),(0,[z0,z2,z3,z8,z524,z16]),(0,[z0,z2,z145,z8,z110,z163]),(0,[z882,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z20,z99,z6]),(0,[z0,z2,z3,z4,z883,z6]),(0,[z0,z2,z3,z276,z20,z6]),(0,[z0,z2,z3,z4,z884,z6]),(0,[z0,z2,z885,z3,z4,z6]),(0,[z23,z0,z3,z241,z8,z76]),(1,[z0,z2,z4,z713,z6])],[(0,[z186,z0,z2,z3,z8,z6]),(0,[z0,z886,z3,z4,z8,z6])]],
   [[(0,[z0,z2,z887,z4,z8,z6]),(0,[z0,z2,z888,z3,z4,z6]),(0,[z0,z2,z200,z133,z8,z6]),(0,[z0,z2,z3,z889,z8,z6]),(0,[z0,z2,z3,z4,z890,z6])],[(0,[z0,z2,z3,z4,z891,z6]),(0,[z0,z2,z3,z4,z892,z6]),(0,[z0,z893,z2,z3,z4,z6]),(0,[z65,z0,z2,z3,z4,z672]),(0,[z0,z45,z3,z4,z731,z6]),(0,[z0,z2,z195,z36,z4,z6]),(0,[z894,z0,z2,z3,z4,z6])],[(0,[z65,z0,z417,z3,z4,z6]),(0,[z0,z233,z490,z3,z8,z6]),(0,[z0,z2,z3,z895,z8,z6]),(0,[z0,z2,z896,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z897]),(0,[z0,z2,z3,z452,z6,z16]),(0,[z0,z2,z332,z20,z8,z6])],[(0,[z98,z230,z2,z3,z4,z6]),(0,[z0,z898,z3,z4,z8,z6]),(0,[z899,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z84,z6,z16]),(0,[z0,z900,z3,z4,z8,z6]),(0,[z901,z2,z3,z8,z6,z16])],[(0,[z109,z2,z3,z813,z8,z6]),(0,[z141,z0,z2,z3,z8,z16]),(0,[z0,z2,z902,z3,z6,z16])],[(0,[z0,z903,z2,z3,z4,z6]),(0,[z0,z2,z3,z8,z210,z6]),(0,[z0,z2,z3,z39,z592,z6]),(0,[z0,z904,z3,z8,z6,z16]),(0,[z905,z2,z3,z8,z6,z16])],[(0,[z906,z0,z2,z3,z4,z8]),(0,[z175,z2,z3,z4,z99,z6]),(0,[z0,z2,z3,z133,z90,z6]),(0,[z100,z2,z3,z20,z8,z58])],[(0,[z0,z2,z3,z8,z6,z907]),(0,[z0,z2,z584,z8,z6,z16]),(0,[z74,z115,z3,z4,z8,z6])]],
   [[],[(0,[z0,z725,z3,z4,z8,z6]),(0,[z0,z2,z3,z908,z8,z6])],[(0,[z45,z55,z3,z4,z32,z6]),(0,[z0,z909,z2,z3,z8,z6]),(0,[z67,z0,z3,z4,z50,z6]),(0,[z266,z0,z2,z52,z8,z6])],[(0,[z0,z2,z3,z4,z910,z6]),(0,[z0,z911,z3,z4,z8,z6])],[(0,[z220,z0,z2,z145,z4,z6]),(0,[z0,z2,z3,z4,z8,z754]),(0,[z0,z2,z4,z8,z6,z912]),(0,[z44,z0,z2,z4,z188,z6])],[(0,[z913,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z914,z6]),(0,[z0,z2,z3,z20,z8,z70]),(0,[z0,z3,z8,z6,z915,z16])],[(0,[z0,z2,z3,z4,z916,z6]),(0,[z0,z2,z3,z8,z6,z917])],[(0,[z55,z3,z4,z354,z8,z6]),(0,[z0,z2,z3,z918,z8,z6]),(0,[z0,z2,z3,z8,z6,z919]),(0,[z0,z2,z3,z4,z920,z6]),(0,[z0,z2,z3,z4,z921,z6]),(0,[z44,z0,z2,z4,z6,z412])]],
   [[(0,[z0,z2,z922,z4,z8,z6]),(0,[z0,z2,z3,z4,z923,z6]),(0,[z393,z0,z2,z3,z4,z31])],[(0,[z0,z2,z3,z924,z8,z6]),(0,[z925,z0,z2,z4,z8,z6]),(0,[z44,z0,z2,z390,z4,z6]),(0,[z0,z2,z3,z39,z751,z6])],[(0,[z0,z2,z3,z8,z926,z6]),(0,[z0,z2,z3,z4,z927,z6]),(0,[z0,z161,z3,z8,z6,z16]),(0,[z0,z2,z3,z241,z8,z6]),(0,[z928,z2,z3,z4,z8,z6]),(0,[z0,z2,z296,z3,z8,z6]),(0,[z0,z2,z3,z20,z890,z6])],[(0,[z0,z2,z4,z8,z6,z929]),(0,[z0,z2,z200,z20,z8,z6])],[(0,[z0,z2,z3,z4,z930,z6]),(0,[z0,z417,z15,z3,z4,z6]),(0,[z0,z2,z3,z4,z713,z6]),(0,[z0,z2,z4,z8,z931,z6]),(0,[z0,z2,z3,z128,z30,z321])],[(0,[z0,z2,z3,z4,z932,z6]),(0,[z0,z2,z3,z933,z8,z6]),(0,[z0,z934,z3,z4,z8,z6]),(0,[z0,z2,z584,z4,z90,z6]),(0,[z0,z2,z3,z4,z6,z935]),(0,[z0,z2,z3,z936,z8,z6]),(0,[z146,z0,z2,z8,z6,z559])],[(0,[z937,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z938,z6]),(0,[z329,z2,z3,z8,z6,z236])],[(0,[z108,z0,z3,z83,z8,z6]),(0,[z0,z2,z740,z3,z6,z16])]],
   [[(0,[z0,z2,z3,z939,z8,z6]),(0,[z0,z940,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z941]),(0,[z0,z2,z3,z239,z8,z16]),(0,[z44,z0,z2,z296,z188,z6])],[(0,[z0,z151,z3,z4,z8,z6]),(0,[z0,z2,z942,z4,z8,z6]),(0,[z943,z0,z2,z3,z8,z6]),(0,[z944,z2,z3,z4,z8,z6]),(0,[z0,z2,z4,z8,z6,z721])],[(0,[z0,z161,z200,z4,z8,z6])],[(0,[z66,z151,z3,z4,z8,z6]),(0,[z945,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z312,z128,z30])],[(0,[z272,z2,z3,z4,z8,z6]),(0,[z617,z2,z89,z4,z8,z6]),(0,[z0,z946,z3,z4,z8,z6]),(0,[z947,z2,z3,z4,z8,z6]),(0,[z0,z115,z3,z201,z8,z353])],[(0,[z0,z2,z948,z4,z8,z6]),(0,[z181,z2,z276,z89,z4,z6]),(0,[z0,z2,z3,z8,z6,z949]),(0,[z950,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z951])],[(0,[z2,z3,z813,z73,z8,z6]),(0,[z44,z0,z2,z20,z188,z6]),(0,[z0,z2,z3,z6,z163,z111]),(0,[z320,z0,z2,z383,z8,z6]),(0,[z0,z2,z3,z4,z128,z780])],[(0,[z0,z2,z3,z4,z952,z6]),(0,[z220,z0,z2,z3,z6,z16])]],
   [[(0,[z0,z115,z3,z4,z8,z396]),(0,[z0,z161,z3,z4,z90,z6]),(0,[z0,z2,z3,z278,z8,z6]),(0,[z0,z2,z3,z4,z452,z6])],[(0,[z0,z34,z2,z145,z4,z6]),(0,[z0,z2,z3,z241,z309,z6]),(0,[z51,z0,z2,z772,z8,z6]),(0,[z0,z2,z3,z128,z30,z16])],[(0,[z627,z0,z3,z4,z50,z6]),(0,[z0,z46,z55,z3,z4,z6]),(0,[z0,z2,z953,z4,z8,z6]),(0,[z0,z2,z3,z4,z954,z6]),(0,[z0,z2,z3,z955,z8,z6]),(0,[z2,z3,z4,z8,z6,z754]),(0,[z0,z2,z529,z8,z6,z16]),(0,[z0,z3,z4,z8,z6,z956])],[(0,[z0,z2,z3,z4,z957,z6]),(0,[z0,z2,z200,z4,z90,z6]),(0,[z0,z2,z958,z4,z8,z6]),(0,[z23,z0,z143,z4,z8,z76]),(0,[z0,z3,z4,z8,z6,z959])],[(0,[z51,z0,z2,z383,z8,z6]),(0,[z0,z2,z3,z960,z8,z6]),(0,[z0,z2,z3,z278,z528,z6]),(1,[z0,z2,z3,z8,z774]),(0,[z0,z961,z3,z8,z6,z16])],[(0,[z74,z2,z3,z4,z8,z6]),(0,[z0,z2,z584,z255,z8,z6]),(0,[z962,z0,z2,z3,z4,z6])],[],[(0,[z0,z963,z3,z4,z8,z6]),(0,[z0,z710,z173,z4,z8,z6])]],
   [[(0,[z0,z233,z237,z3,z8,z6]),(0,[z10,z0,z173,z8,z6,z16]),(0,[z2,z3,z4,z8,z6,z964])],[(0,[z0,z2,z3,z965,z8,z6]),(0,[z966,z0,z2,z3,z8,z6]),(0,[z0,z2,z967,z4,z8,z6]),(0,[z51,z0,z2,z301,z8,z6]),(0,[z0,z233,z3,z349,z8,z6]),(0,[z189,z0,z2,z4,z8,z77])],[(0,[z0,z2,z145,z4,z8,z540]),(0,[z968,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z8,z284,z16]),(0,[z0,z2,z3,z4,z969,z6]),(0,[z0,z2,z3,z40,z6,z569])],[(0,[z0,z45,z3,z4,z487,z6]),(0,[z0,z151,z3,z20,z8,z6]),(0,[z0,z417,z3,z8,z6,z16]),(0,[z0,z2,z3,z8,z970,z6]),(0,[z0,z2,z971,z4,z8,z6]),(0,[z0,z2,z52,z135,z3,z6]),(0,[z0,z2,z3,z972,z8,z6]),(0,[z266,z0,z2,z20,z8,z6])],[(1,[z2,z881,z4,z8,z6]),(0,[z0,z19,z710,z4,z8,z6]),(0,[z0,z2,z3,z8,z466,z16]),(0,[z0,z2,z3,z312,z8,z6])],[(0,[z121,z2,z3,z4,z8,z388]),(0,[z0,z2,z3,z4,z973,z6]),(0,[z0,z2,z3,z8,z974,z6]),(0,[z0,z2,z3,z4,z6,z975]),(1,[z44,z0,z2,z296,z6])],[(0,[z0,z45,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z807]),(0,[z2,z3,z171,z813,z8,z6]),(0,[z0,z34,z2,z3,z281,z6]),(0,[z0,z2,z3,z976,z8,z6]),(0,[z0,z45,z2,z332,z4,z6]),(0,[z272,z2,z3,z20,z8,z6]),(0,[z24,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z316,z8,z6])],[(0,[z0,z2,z3,z4,z977,z6]),(0,[z0,z2,z3,z528,z6,z163]),(0,[z266,z0,z2,z39,z4,z6])]],
   [[(0,[z66,z2,z3,z167,z6,z16]),(0,[z0,z161,z3,z255,z8,z6]),(0,[z0,z2,z3,z8,z344,z16]),(0,[z0,z2,z3,z4,z128,z435]),(0,[z0,z2,z978,z3,z8,z6])],[(0,[z120,z2,z3,z599,z8,z6]),(0,[z260,z3,z4,z8,z6,z58]),(0,[z0,z2,z200,z4,z101,z6]),(0,[z0,z2,z979,z4,z8,z6]),(0,[z0,z2,z332,z4,z6,z31]),(0,[z0,z980,z3,z4,z8,z6])],[(0,[z0,z2,z38,z36,z8,z6])],[(0,[z981,z0,z2,z3,z8,z6]),(0,[z0,z2,z200,z255,z8,z6])],[(0,[z109,z2,z644,z3,z8,z6]),(0,[z982,z2,z3,z4,z8,z6]),(0,[z0,z34,z2,z3,z6,z16]),(0,[z74,z2,z3,z4,z309,z6]),(0,[z0,z2,z772,z37,z8,z6]),(0,[z0,z2,z4,z8,z340,z6]),(0,[z189,z0,z2,z190,z8,z77]),(0,[z664,z0,z2,z3,z8,z16])],[(0,[z0,z2,z3,z276,z6,z16]),(0,[z0,z983,z2,z3,z4,z6]),(0,[z0,z94,z3,z29,z8,z6])],[(0,[z175,z2,z3,z4,z8,z6]),(0,[z151,z3,z4,z32,z8,z6]),(0,[z104,z2,z3,z4,z460,z6]),(0,[z100,z2,z3,z133,z8,z58]),(0,[z0,z984,z2,z3,z4,z6]),(0,[z44,z0,z2,z394,z4,z6]),(0,[z0,z2,z3,z8,z6,z985]),(0,[z0,z3,z8,z6,z16,z956])],[(0,[z0,z2,z3,z4,z986,z6]),(0,[z0,z2,z3,z8,z6,z987]),(0,[z0,z2,z143,z4,z8,z6]),(0,[z74,z2,z3,z20,z8,z6]),(0,[z0,z2,z3,z8,z6,z988]),(0,[z0,z2,z3,z8,z6,z989]),(0,[z0,z2,z164,z41,z8,z6])]],
   [[(0,[z0,z2,z3,z990,z8,z6]),(0,[z10,z0,z351,z173,z8,z6]),(0,[z0,z2,z3,z4,z991,z6]),(1,[z266,z0,z2,z52,z6]),(0,[z266,z0,z2,z52,z4,z6]),(0,[z0,z2,z3,z8,z774,z16])],[(0,[z0,z2,z992,z3,z8,z6]),(0,[z44,z0,z417,z3,z4,z6]),(0,[z0,z2,z4,z8,z6,z993]),(0,[z0,z2,z3,z255,z90,z6]),(0,[z994,z0,z2,z3,z8,z6]),(0,[z272,z3,z4,z50,z8,z6]),(0,[z65,z0,z2,z3,z4,z780])],[(0,[z104,z2,z3,z4,z830,z6]),(0,[z0,z260,z3,z133,z8,z6]),(0,[z0,z233,z3,z767,z8,z6]),(0,[z0,z2,z995,z4,z8,z6]),(0,[z0,z2,z3,z4,z996,z6]),(0,[z0,z2,z997,z3,z20,z6])],[(0,[z0,z260,z3,z4,z8,z6]),(0,[z0,z2,z529,z241,z8,z6]),(0,[z189,z0,z2,z20,z8,z77])],[(0,[z0,z2,z3,z4,z998,z6]),(0,[z44,z0,z2,z35,z4,z6]),(0,[z67,z175,z3,z4,z50,z6]),(0,[z0,z2,z3,z999,z8,z6]),(0,[z0,z2,z4,z528,z6,z77]),(0,[z0,z2,z3,z20,z8,z246]),(0,[z0,z2,z3,z20,z969,z6])],[(0,[z0,z2,z3,z8,z6,z1000]),(0,[z0,z2,z3,z1001,z8,z6]),(0,[z0,z2,z3,z1002,z8,z6]),(0,[z104,z2,z3,z4,z32,z6]),(0,[z0,z2,z3,z1003,z8,z6]),(0,[z0,z2,z529,z247,z8,z6]),(0,[z0,z2,z195,z3,z4,z6]),(0,[z1004,z2,z3,z4,z8,z6])],[(0,[z1005,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z1006,z8,z6]),(0,[z0,z1007,z3,z4,z8,z6]),(0,[z0,z1008,z2,z3,z4,z6]),(0,[z0,z2,z325,z3,z116,z6])],[(0,[z0,z2,z3,z8,z341,z16]),(0,[z0,z2,z3,z4,z1009,z6]),(0,[z0,z2,z3,z499,z8,z16]),(0,[z0,z2,z1010,z4,z8,z6]),(0,[z44,z0,z2,z4,z676,z6])]],
   [[(0,[z0,z2,z3,z4,z1011,z6]),(0,[z0,z2,z3,z1012,z8,z6]),(0,[z329,z2,z3,z73,z8,z6]),(0,[z0,z2,z3,z90,z6,z16]),(0,[z1013,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z8,z774])],[(0,[z0,z2,z3,z1014,z8,z6])],[(0,[z0,z55,z3,z4,z53,z6]),(0,[z2,z3,z881,z4,z8,z6]),(0,[z401,z0,z3,z4,z50,z6])],[(0,[z1015,z0,z2,z3,z8,z6]),(0,[z0,z2,z1016,z4,z8,z6])],[(1,[z2,z3,z4,z830,z6]),(0,[z121,z2,z3,z8,z57,z16]),(0,[z0,z2,z3,z309,z6,z16])],[(0,[z657,z0,z3,z4,z8,z76]),(0,[z100,z2,z584,z4,z8,z58]),(0,[z24,z2,z529,z4,z8,z6]),(0,[z0,z2,z3,z20,z6,z75])],[(0,[z0,z2,z3,z4,z1017,z6]),(0,[z0,z2,z1018,z3,z8,z6]),(0,[z0,z2,z3,z1019,z8,z6]),(1,[z2,z3,z813,z8,z6]),(0,[z0,z2,z143,z4,z309,z6]),(0,[z0,z2,z3,z4,z6,z1020])],[(0,[z0,z2,z3,z8,z6,z1021]),(0,[z0,z2,z3,z255,z101,z6]),(0,[z0,z2,z145,z4,z8,z439]),(0,[z0,z2,z3,z1022,z8,z6]),(0,[z0,z2,z1023,z4,z8,z6]),(0,[z44,z0,z2,z296,z8,z6]),(0,[z811,z0,z2,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z1024,z8,z6]),(0,[z1025,z0,z2,z3,z8,z6]),(0,[z0,z3,z4,z50,z731,z6]),(0,[z0,z2,z4,z8,z713,z6]),(0,[z0,z2,z3,z1026,z8,z6])],[(0,[z0,z2,z3,z1027,z8,z6]),(0,[z0,z260,z584,z4,z8,z6]),(0,[z0,z2,z143,z20,z8,z6])],[(0,[z0,z2,z3,z1028,z8,z6]),(0,[z0,z2,z3,z1029,z8,z6]),(0,[z0,z1030,z3,z4,z8,z6]),(0,[z120,z174,z2,z3,z8,z6]),(0,[z100,z2,z3,z8,z58,z16]),(0,[z855,z2,z3,z8,z6,z16])],[(0,[z1031,z0,z2,z4,z8,z6]),(0,[z0,z2,z3,z4,z1032,z6]),(0,[z23,z0,z3,z4,z8,z76]),(0,[z266,z0,z2,z52,z116,z6])],[(0,[z0,z2,z15,z273,z4,z6]),(0,[z0,z2,z3,z4,z1033,z6])],[(0,[z117,z55,z3,z8,z6,z16]),(0,[z0,z2,z3,z8,z374,z16]),(0,[z0,z260,z3,z20,z8,z6]),(0,[z0,z351,z34,z2,z3,z6]),(0,[z0,z2,z1034,z4,z8,z6]),(0,[z1035,z0,z2,z3,z4,z6])],[(0,[z0,z2,z1036,z4,z8,z6]),(1,[z0,z710,z4,z8,z6]),(0,[z0,z2,z3,z1037,z4,z6]),(0,[z0,z3,z767,z4,z8,z6]),(0,[z74,z2,z529,z4,z8,z6]),(0,[z0,z2,z20,z8,z931,z6]),(0,[z0,z2,z3,z4,z128,z30])],[(0,[z104,z2,z3,z20,z32,z6]),(0,[z182,z0,z173,z4,z8,z6])]],
   [[(0,[z0,z2,z3,z8,z593,z16]),(0,[z100,z161,z3,z4,z8,z58]),(0,[z0,z2,z3,z1038,z4,z6]),(0,[z0,z2,z3,z8,z6,z406])],[(0,[z0,z2,z4,z8,z1039,z6]),(0,[z0,z2,z3,z8,z1040,z6]),(0,[z66,z2,z3,z4,z223,z6]),(0,[z0,z45,z507,z3,z4,z6])],[(0,[z216,z0,z2,z3,z4,z31]),(0,[z0,z3,z4,z731,z8,z6]),(0,[z23,z0,z3,z4,z75,z76]),(0,[z0,z2,z3,z20,z8,z774])],[(0,[z0,z2,z3,z4,z1041,z6]),(0,[z44,z0,z2,z4,z579,z6])],[(0,[z0,z2,z3,z8,z6,z1042]),(0,[z0,z2,z3,z1043,z4,z6]),(0,[z0,z2,z3,z241,z84,z6]),(0,[z0,z839,z3,z4,z8,z6])],[(0,[z0,z2,z3,z1044,z8,z6]),(0,[z0,z2,z3,z8,z6,z576]),(0,[z0,z2,z1045,z4,z8,z6]),(0,[z0,z2,z1046,z3,z8,z6]),(0,[z0,z2,z3,z1047,z8,z6]),(0,[z1048,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z1049,z6]),(0,[z104,z2,z3,z85,z4,z6]),(0,[z0,z2,z3,z247,z84,z6])],[(0,[z0,z2,z407,z3,z8,z6]),(0,[z66,z2,z3,z4,z487,z6]),(0,[z0,z2,z3,z53,z6,z16]),(0,[z422,z0,z2,z3,z8,z16]),(0,[z0,z2,z3,z8,z6,z1050]),(0,[z0,z2,z3,z8,z6,z1051]),(0,[z0,z2,z145,z4,z528,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z200,z8,z6,z16]),(0,[z0,z2,z3,z8,z355,z16]),(0,[z0,z3,z83,z767,z8,z6]),(0,[z0,z3,z4,z8,z353,z761])],[(0,[z0,z2,z3,z62,z6,z16]),(0,[z0,z2,z1052,z4,z8,z6]),(0,[z100,z2,z3,z4,z90,z58]),(0,[z0,z2,z3,z281,z8,z6]),(0,[z0,z2,z3,z4,z1053,z6]),(0,[z175,z2,z3,z4,z30,z6]),(0,[z0,z2,z3,z20,z8,z25]),(0,[z0,z2,z296,z71,z8,z6]),(0,[z0,z2,z4,z8,z6,z1054])],[(0,[z98,z2,z3,z4,z62,z6]),(0,[z0,z2,z4,z8,z6,z1055]),(0,[z0,z19,z11,z4,z8,z6]),(0,[z0,z351,z2,z3,z527,z6]),(0,[z23,z0,z3,z4,z309,z76]),(0,[z51,z0,z2,z196,z8,z6])],[(0,[z0,z2,z3,z4,z1056,z6]),(0,[z0,z2,z1057,z3,z8,z6]),(0,[z0,z2,z3,z48,z6,z569]),(0,[z0,z2,z997,z3,z4,z6])],[(0,[z0,z2,z1058,z3,z8,z6]),(0,[z132,z2,z88,z4,z8,z6]),(0,[z0,z2,z3,z4,z1059,z6]),(0,[z1060,z0,z2,z3,z4,z6]),(0,[z51,z0,z2,z195,z37,z6]),(0,[z65,z0,z2,z3,z16,z31])],[(0,[z867,z0,z2,z4,z8,z6]),(0,[z82,z0,z226,z3,z8,z6]),(0,[z23,z0,z3,z20,z8,z76]),(0,[z0,z2,z3,z20,z8,z287]),(0,[z199,z2,z3,z179,z8,z6])],[(0,[z119,z0,z2,z3,z276,z6]),(0,[z66,z2,z3,z4,z167,z6]),(0,[z1061,z2,z3,z4,z8,z6]),(0,[z65,z175,z2,z3,z4,z6]),(0,[z0,z2,z3,z1062,z8,z6]),(0,[z24,z2,z3,z4,z84,z6]),(1,[z0,z2,z4,z8,z721])],[(0,[z0,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z360,z16]),(0,[z0,z2,z195,z3,z20,z6]),(0,[z1063,z0,z2,z4,z8,z6])]],
   [[(1,[z0,z2,z772,z8,z6]),(0,[z0,z2,z296,z15,z3,z6]),(0,[z1064,z0,z2,z3,z8,z6]),(0,[z0,z2,z325,z3,z6,z297]),(0,[z0,z2,z3,z20,z128,z30])],[(0,[z444,z0,z2,z4,z8,z77])],[(0,[z0,z2,z3,z4,z722,z6]),(0,[z0,z2,z3,z1065,z8,z6]),(0,[z0,z2,z3,z4,z6,z852])],[(0,[z51,z0,z2,z37,z8,z6]),(0,[z51,z0,z2,z195,z8,z6])],[(0,[z1066,z0,z2,z3,z4,z8]),(0,[z0,z2,z3,z1067,z8,z6]),(0,[z104,z2,z3,z32,z6,z16]),(0,[z0,z2,z3,z20,z8,z81]),(0,[z23,z24,z3,z4,z8,z76]),(0,[z0,z1068,z2,z3,z4,z6])],[(0,[z0,z2,z3,z1069,z8,z6]),(0,[z0,z2,z38,z364,z8,z6]),(0,[z0,z2,z1070,z4,z8,z6]),(0,[z0,z2,z3,z4,z30,z256]),(0,[z0,z115,z3,z8,z353,z16]),(0,[z0,z2,z3,z8,z438,z16]),(0,[z0,z2,z3,z8,z1071,z6]),(0,[z0,z2,z3,z20,z8,z93])],[(0,[z0,z1072,z3,z4,z8,z6]),(0,[z67,z272,z3,z4,z50,z6])],[(0,[z66,z55,z3,z4,z50,z6]),(0,[z0,z2,z3,z99,z6,z16]),(0,[z0,z2,z3,z1073,z8,z6]),(0,[z619,z2,z3,z4,z32,z6]),(0,[z100,z2,z3,z4,z101,z58]),(1,[z2,z3,z4,z8,z754]),(0,[z121,z2,z3,z152,z8,z57]),(0,[z0,z2,z3,z4,z6,z1074]),(0,[z0,z618,z3,z4,z68,z6]),(0,[z74,z2,z3,z4,z84,z6]),(0,[z0,z2,z195,z38,z3,z6]),(0,[z44,z0,z2,z296,z3,z6])]],
   [[(0,[z0,z2,z3,z8,z6,z1075]),(0,[z2,z88,z881,z4,z8,z6]),(0,[z0,z2,z145,z4,z8,z721])],[(0,[z0,z2,z3,z1076,z8,z6]),(0,[z66,z0,z2,z332,z4,z6]),(0,[z0,z2,z3,z1077,z8,z6]),(0,[z0,z2,z3,z1078,z8,z6]),(0,[z100,z2,z3,z255,z8,z58]),(0,[z1079,z2,z3,z4,z8,z6]),(0,[z901,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z1080,z6]),(0,[z0,z2,z3,z20,z5,z6]),(0,[z0,z2,z1081,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z1082]),(0,[z51,z44,z0,z2,z52,z6])],[(0,[z0,z2,z3,z1083,z8,z6]),(0,[z0,z904,z3,z4,z8,z6]),(0,[z0,z1084,z3,z4,z8,z6]),(0,[z0,z260,z3,z4,z101,z6]),(0,[z905,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z163]),(0,[z0,z2,z3,z20,z1053,z6])],[(0,[z0,z2,z3,z4,z1085,z6]),(0,[z0,z2,z3,z8,z6,z1086]),(0,[z0,z2,z3,z4,z1087,z6]),(0,[z0,z19,z11,z20,z8,z6]),(0,[z0,z1088,z2,z3,z8,z6]),(0,[z0,z3,z4,z8,z761,z76]),(0,[z0,z2,z3,z8,z6,z1089]),(0,[z0,z2,z3,z4,z8,z780])],[(0,[z0,z2,z1090,z3,z8,z6]),(0,[z0,z2,z3,z4,z1091,z6]),(0,[z0,z3,z4,z8,z6,z1092]),(0,[z0,z2,z1093,z3,z8,z6])],[(0,[z0,z2,z3,z4,z1094,z6]),(0,[z132,z2,z88,z20,z8,z6]),(0,[z0,z2,z3,z4,z6,z1095]),(0,[z230,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z309,z6])],[(0,[z104,z417,z3,z4,z32,z6]),(0,[z0,z2,z3,z8,z6,z1096]),(0,[z0,z2,z1097,z4,z8,z6]),(0,[z0,z2,z3,z4,z1098,z6]),(0,[z0,z2,z1099,z3,z8,z6]),(0,[z0,z2,z3,z6,z16,z111])]],
   [[(0,[z653,z55,z3,z4,z8,z6]),(0,[z249,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1100,z6]),(0,[z66,z2,z3,z20,z167,z6]),(0,[z266,z0,z2,z8,z6,z16])],[(0,[z0,z2,z3,z20,z8,z6]),(0,[z0,z2,z145,z4,z110,z111]),(0,[z1063,z0,z2,z20,z8,z6])],[(0,[z181,z2,z881,z4,z8,z6]),(0,[z51,z0,z2,z263,z8,z6]),(0,[z561,z0,z2,z3,z8,z16]),(0,[z0,z2,z145,z4,z8,z435]),(0,[z0,z2,z145,z278,z8,z110])],[(0,[z0,z2,z3,z101,z6,z16]),(0,[z0,z2,z3,z4,z6,z1101]),(0,[z67,z0,z3,z4,z731,z6]),(0,[z24,z2,z3,z8,z6,z16]),(0,[z0,z2,z3,z1102,z8,z6])],[(0,[z0,z2,z3,z4,z1103,z6]),(0,[z66,z2,z3,z4,z425,z6]),(0,[z0,z2,z3,z4,z6,z437]),(0,[z604,z2,z3,z4,z32,z6]),(0,[z23,z0,z529,z4,z8,z76]),(0,[z0,z2,z3,z4,z8,z721])],[(0,[z0,z3,z4,z50,z5,z6]),(0,[z0,z1104,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z1105]),(0,[z0,z115,z3,z4,z8,z761]),(0,[z0,z2,z3,z20,z452,z6]),(0,[z44,z0,z2,z296,z4,z6])],[(0,[z0,z2,z3,z20,z8,z150]),(0,[z175,z2,z3,z4,z167,z6]),(0,[z0,z2,z3,z4,z1106,z6]),(0,[z0,z2,z3,z772,z8,z6]),(0,[z0,z2,z4,z71,z713,z6]),(0,[z0,z2,z176,z8,z6,z500]),(0,[z0,z42,z3,z349,z8,z6]),(0,[z108,z0,z3,z334,z8,z6]),(0,[z0,z2,z191,z3,z517,z6])],[(0,[z0,z2,z3,z8,z6,z1107]),(0,[z0,z2,z3,z1108,z8,z6]),(0,[z1109,z2,z3,z4,z8,z6]),(0,[z319,z2,z3,z8,z6,z72])]],
   [[(0,[z0,z2,z3,z1110,z8,z6]),(0,[z0,z3,z767,z29,z8,z6]),(0,[z1111,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z4,z6,z361]),(0,[z0,z2,z3,z1112,z8,z6])],[(0,[z404,z55,z3,z4,z8,z6]),(0,[z0,z2,z1113,z4,z8,z6]),(0,[z0,z2,z143,z4,z84,z6])],[(0,[z0,z1114,z2,z3,z8,z6]),(0,[z23,z0,z3,z8,z76,z16]),(0,[z0,z2,z3,z8,z6,z1115]),(0,[z189,z0,z2,z139,z8,z77]),(0,[z0,z3,z8,z6,z16,z959]),(0,[z442,z2,z3,z180,z8,z6])],[(0,[z0,z2,z3,z1116,z8,z6]),(0,[z0,z2,z3,z1117,z8,z6]),(0,[z0,z2,z3,z1118,z4,z6])],[(0,[z0,z2,z3,z1119,z8,z6]),(0,[z0,z2,z4,z8,z6,z1120]),(0,[z44,z0,z2,z4,z208,z6])],[(0,[z0,z1121,z3,z4,z8,z6]),(0,[z0,z2,z332,z8,z6,z321])],[(0,[z181,z2,z89,z8,z6,z16]),(0,[z0,z2,z3,z4,z1122,z6]),(0,[z0,z2,z4,z71,z519,z6]),(1,[z0,z2,z3,z4,z780])],[(0,[z0,z11,z710,z4,z8,z6]),(0,[z0,z2,z38,z8,z496,z6]),(0,[z821,z0,z2,z8,z6,z16]),(0,[z0,z2,z3,z20,z1091,z6])]],
   [[(0,[z0,z2,z3,z1123,z8,z6]),(0,[z0,z2,z3,z20,z309,z6]),(0,[z2,z3,z4,z8,z6,z790]),(0,[z0,z2,z3,z8,z1124,z6])],[(0,[z0,z2,z3,z4,z1125,z6]),(0,[z0,z2,z38,z8,z6,z500]),(0,[z0,z2,z3,z8,z6,z774])],[(0,[z0,z2,z3,z5,z6,z16]),(0,[z0,z2,z3,z20,z8,z204]),(0,[z1126,z2,z3,z4,z8,z6]),(0,[z0,z2,z15,z71,z6,z16])],[(1,[z0,z3,z4,z8,z761]),(0,[z51,z0,z2,z195,z3,z6]),(0,[z0,z2,z3,z1127,z8,z6])],[(0,[z0,z2,z4,z8,z1128,z6])],[(0,[z0,z2,z3,z1129,z4,z6]),(0,[z0,z1130,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z1131,z6]),(0,[z0,z2,z3,z4,z1132,z6]),(0,[z23,z0,z46,z3,z4,z76])],[(0,[z0,z2,z3,z20,z6,z437]),(0,[z0,z2,z3,z527,z4,z6])],[(0,[z0,z2,z3,z8,z6,z1133]),(0,[z65,z0,z2,z3,z4,z392]),(0,[z1134,z0,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z832])]],
   [[(0,[z0,z1135,z3,z4,z8,z6]),(0,[z0,z2,z529,z4,z8,z6]),(0,[z0,z2,z3,z1136,z8,z6])],[(0,[z0,z2,z3,z4,z1137,z6]),(0,[z1138,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z1139,z6]),(0,[z0,z2,z3,z1140,z8,z6]),(0,[z1141,z2,z3,z4,z8,z6]),(0,[z0,z2,z3,z1142,z8,z6])],[(0,[z0,z417,z3,z4,z5,z6]),(0,[z181,z2,z229,z89,z8,z6]),(0,[z0,z2,z3,z1143,z8,z6]),(0,[z109,z2,z3,z179,z8,z6]),(0,[z0,z2,z3,z1144,z8,z6]),(0,[z0,z961,z3,z4,z8,z6]),(0,[z0,z2,z332,z8,z6,z16])],[(0,[z0,z351,z2,z3,z8,z6]),(0,[z175,z2,z3,z20,z8,z6]),(0,[z0,z3,z4,z8,z6,z761]),(0,[z0,z2,z145,z8,z110,z16])],[(0,[z121,z2,z3,z4,z8,z754]),(0,[z0,z2,z3,z1145,z8,z6]),(0,[z24,z2,z3,z241,z8,z6])],[(0,[z119,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z8,z6,z1146]),(0,[z23,z0,z3,z4,z84,z76]),(0,[z0,z2,z3,z39,z40,z6])],[(0,[z0,z2,z881,z4,z8,z6]),(0,[z0,z417,z3,z4,z167,z6]),(0,[z10,z0,z173,z4,z8,z6]),(0,[z0,z2,z3,z8,z6,z1147]),(0,[z24,z2,z3,z247,z8,z6])],[(0,[z0,z2,z3,z4,z101,z6]),(0,[z2,z3,z4,z8,z6,z1148]),(0,[z0,z2,z3,z4,z30,z780])]],
   [[(0,[z0,z2,z3,z1149,z8,z6]),(0,[z230,z0,z2,z3,z20,z6]),(0,[z0,z2,z8,z340,z6,z16]),(0,[z0,z2,z8,z6,z16,z1120]),(0,[z0,z2,z3,z20,z1122,z6])],[(0,[z0,z417,z3,z4,z8,z6])],[(0,[z0,z3,z4,z8,z6,z915]),(0,[z0,z260,z3,z8,z6,z16])],[(0,[z51,z0,z2,z511,z8,z6]),(0,[z2,z3,z4,z830,z167,z6]),(0,[z1150,z0,z2,z3,z8,z6]),(0,[z0,z2,z3,z4,z8,z1151]),(0,[z0,z2,z3,z1152,z8,z6]),(0,[z0,z2,z3,z20,z8,z245])],[(0,[z0,z2,z3,z4,z6,z1153]),(0,[z0,z1154,z3,z4,z8,z6]),(0,[z0,z2,z3,z1155,z8,z6]),(0,[z0,z2,z312,z8,z6,z125])],[(0,[z0,z2,z3,z8,z1156,z6]),(0,[z44,z175,z2,z3,z4,z6]),(0,[z0,z2,z1157,z4,z8,z6])],[(0,[z2,z3,z4,z830,z8,z6]),(0,[z66,z684,z2,z3,z4,z6]),(0,[z100,z2,z200,z4,z8,z58]),(0,[z0,z2,z3,z20,z8,z674]),(0,[z1158,z0,z2,z3,z8,z6]),(0,[z0,z2,z195,z3,z6,z16]),(0,[z0,z2,z4,z8,z6,z125])],[(0,[z725,z55,z3,z4,z8,z6]),(0,[z0,z215,z3,z4,z50,z6]),(0,[z0,z2,z3,z1159,z8,z6]),(0,[z67,z0,z3,z4,z223,z6]),(0,[z0,z2,z1160,z3,z4,z6]),(0,[z0,z2,z3,z1161,z8,z6]),(0,[z82,z0,z3,z8,z6,z647]),(0,[z0,z2,z529,z4,z309,z6]),(0,[z0,z2,z4,z772,z8,z6]),(0,[z189,z0,z2,z8,z77,z16])]],
   [[(0,[z55,z3,z4,z8,z6,z668]),(0,[z0,z2,z3,z4,z8,z1162]),(0,[z0,z2,z3,z4,z1163,z6])],[(0,[z0,z46,z2,z3,z4,z6]),(0,[z175,z2,z3,z4,z50,z6]),(0,[z0,z2,z3,z4,z128,z571])],[(0,[z0,z2,z3,z4,z1164,z6]),(0,[z0,z2,z3,z1165,z8,z6]),(0,[z0,z260,z200,z4,z8,z6]),(0,[z0,z2,z1166,z4,z8,z6]),(0,[z0,z2,z529,z20,z8,z6]),(0,[z0,z2,z885,z3,z6,z16])],[(0,[z0,z2,z3,z4,z1167,z6]),(0,[z2,z3,z4,z8,z6,z748]),(0,[z67,z0,z3,z4,z6,z485])],[(0,[z2,z881,z89,z4,z8,z6])],[(0,[z0,z2,z4,z8,z1168,z6]),(0,[z0,z2,z3,z1169,z8,z6]),(0,[z0,z2,z3,z8,z1170,z6])],[(0,[z0,z2,z3,z4,z1171,z6]),(0,[z0,z45,z3,z4,z68,z6]),(0,[z0,z2,z4,z713,z188,z6])],[(0,[z0,z2,z3,z4,z53,z6]),(0,[z175,z2,z3,z4,z68,z6])]],
   [[(0,[z0,z2,z3,z1172,z8,z6]),(0,[z0,z260,z3,z4,z90,z6]),(0,[z10,z0,z173,z20,z8,z6]),(0,[z0,z2,z3,z8,z6,z1173]),(0,[z0,z2,z3,z4,z6,z1174]),(0,[z67,z0,z2,z332,z4,z6]),(0,[z0,z2,z3,z278,z6,z111])],[(0,[z0,z2,z3,z133,z8,z6]),(0,[z0,z2,z3,z8,z6,z1175]),(0,[z0,z2,z710,z4,z8,z6]),(0,[z82,z0,z3,z83,z8,z6]),(0,[z0,z2,z3,z4,z84,z6]),(0,[z0,z1176,z2,z3,z8,z6]),(0,[z0,z2,z4,z8,z721,z77])],[(0,[z117,z407,z55,z3,z8,z6]),(0,[z0,z2,z3,z4,z6,z1177]),(0,[z0,z2,z332,z4,z128,z6])],[(0,[z0,z417,z3,z20,z8,z6]),(0,[z0,z2,z3,z6,z437,z16]),(0,[z0,z45,z512,z3,z4,z6]),(0,[z2,z3,z8,z6,z16,z1148]),(0,[z0,z2,z3,z8,z246,z774]),(0,[z65,z0,z2,z3,z103,z31])],[(0,[z92,z2,z88,z4,z8,z6]),(0,[z0,z2,z52,z3,z263,z6]),(0,[z0,z2,z3,z103,z8,z6])],[(0,[z1178,z0,z2,z3,z8,z6]),(0,[z230,z2,z55,z3,z4,z6]),(0,[z0,z45,z3,z68,z6,z16]),(0,[z1179,z2,z3,z4,z8,z6])],[(0,[z0,z2,z3,z1180,z8,z6]),(0,[z0,z1,z3,z4,z53,z6]),(0,[z0,z1181,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z30,z423]),(0,[z0,z2,z3,z4,z528,z6])],[(0,[z0,z2,z3,z40,z240,z6])]],
   [[(0,[z0,z2,z3,z813,z8,z6]),(0,[z66,z2,z3,z4,z830,z6]),(0,[z66,z484,z2,z3,z4,z6]),(0,[z2,z3,z4,z32,z830,z6]),(0,[z0,z2,z3,z527,z20,z6])],[(0,[z0,z2,z3,z4,z1182,z6])],[(0,[z0,z2,z1183,z4,z8,z6]),(0,[z0,z2,z3,z751,z116,z6])],[(0,[z2,z3,z4,z32,z99,z6]),(0,[z220,z0,z2,z3,z229,z6]),(0,[z0,z2,z3,z1184,z4,z6]),(0,[z0,z2,z902,z3,z4,z6])],[(0,[z0,z2,z3,z1185,z8,z6]),(0,[z0,z2,z3,z4,z8,z1186])],[(0,[z2,z725,z3,z4,z8,z6]),(0,[z609,z55,z3,z4,z8,z6]),(0,[z0,z2,z3,z8,z106,z16]),(0,[z0,z2,z3,z190,z8,z6]),(0,[z0,z94,z3,z8,z6,z411]),(0,[z0,z2,z3,z20,z1167,z6])],[(0,[z0,z2,z3,z1187,z8,z6])],[(0,[z1188,z0,z2,z3,z8,z6]),(0,[z0,z1189,z3,z4,z8,z6]),(0,[z0,z2,z584,z133,z8,z6]),(0,[z100,z2,z3,z4,z437,z58])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 533).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1068).take 151) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1219)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [533, 535, 151] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 117).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 229).take 27).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [117, 112, 27] = true :=
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

end PEqualNP.Outside.L_meta_45924

theorem PEqualNP.Outside.L_meta_45924 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4007701152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4007701152) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45924.solve