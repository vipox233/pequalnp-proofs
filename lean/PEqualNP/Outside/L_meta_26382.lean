import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26382

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

section Live

variable {α : Type} [DecidableEq α] (bop : α → α → Finset α) (uop : α → Finset α) (goal : α)

def build : ℕ → Finset α → Prop
  | 0, av => goal ∈ av
  | k + 1, av => build k av ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ bop a b, build k (insert z av)) ∨
      (∃ a ∈ av, ∃ z ∈ uop a, build k (insert z av))

def live : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live k s ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ bop a b, z ∉ s ∧
        ∃ rest : Finset α, s = insert a (insert b rest) ∧ live k (insert z rest)) ∨
      (∃ a ∈ s, ∃ z ∈ uop a, z ∉ s ∧
        ∃ rest : Finset α, s = insert a rest ∧ live k (insert z rest))

variable {bop uop goal}

theorem compress {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∃ s ⊆ av, live bop uop goal k s := by
  induction k generalizing av with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩ | ⟨a, ha, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr (Or.inl ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨s, hs, Or.inr (Or.inr ⟨a, by simp [s], z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

theorem live_separates (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b) (hun : ∀ a, ∀ z ∈ uop a, D z → D a)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, hun a w hz hD⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem live_tight (D : α → Prop) (hd : D goal)
    (hops : ∀ a b, ∀ z ∈ bop a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live bop uop goal k s) (hc : s.card = k + 1) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩ |
        ⟨a, ha, z, hz, hout, rest, rfl, tail⟩
    · have := live_card skip
      omega
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      have hc' : (insert z rest).card = k + 1 := by
        rw [Finset.card_insert_of_notMem hzrest]; omega
      obtain ⟨w, hw, hD⟩ := ih tail hc'
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega

theorem build_mono {k : ℕ} {av : Finset α} (h : build bop uop goal k av) :
    ∀ j, k ≤ j → build bop uop goal j av := by
  intro j hj
  induction hj with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Live

section Lists

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

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
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

theorem recover_kept1 {ws r : List ℕ} {a : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : (v ∈ insert a r.toFinset) ↔ v ∈ insert a needed := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List ℕ} {goal : ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

theorem all_of_chunks {β : Type} (L : List β) (f : β → Bool) (B n : ℕ) (hlen : L.length ≤ B * n)
    (h : ∀ i < n, ((L.drop (B * i)).take B).all f = true) : L.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · subst h0; rw [Nat.zero_mul] at hlen; omega
    · exact h0
  have hi : j / B < n := by
    rw [Nat.div_lt_iff_lt_mul hB]; rw [Nat.mul_comm] at hlen; omega
  have hmod := Nat.mod_lt j hB
  have hdm := Nat.div_add_mod j B
  have hc := List.all_eq_true.mp (h (j / B) hi)
  apply hc
  rw [List.mem_iff_getElem]
  refine ⟨j % B, ?_, ?_⟩
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    all_goals omega

end Lists

section Search

def enc : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * enc l

theorem testBit_enc (l : List Bool) (i : ℕ) : (enc l).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp [enc]
  | cons b l ih =>
    cases i with
    | zero =>
      simp only [enc, Nat.testBit_zero, List.getD_cons_zero]
      cases b <;> simp <;> omega
    | succ i =>
      rw [Nat.testBit_add_one, List.getD_cons_succ, ← ih i]
      congr 1
      simp only [enc]
      cases b <;> simp <;> omega

def maskN (N : ℕ) : ℕ := enc (List.replicate N true)

theorem maskN_testBit (N r : ℕ) : (maskN N).testBit r = decide (r < N) := by
  rw [maskN, testBit_enc]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  by_cases h : r < N <;> simp [h]

variable (goal mask : ℕ) (prs : List (ℕ × ℕ)) (N J : ℕ)

def prsOf : List (ℕ × ℕ) := (List.range J).map (fun j => (N + j, N + J + j))

def sepF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) ^^^ (w >>> (N + J)))) 0 &&& maskN J) == maskN J

def monF (ws : List ℕ) : Bool :=
  (ws.foldr (fun w acc => acc ||| ((w >>> N) &&& (maskN J ^^^ (w >>> (N + J))))) 0 &&& maskN J)
    == maskN J

theorem foldr_or_testBit (f : ℕ → ℕ) (ws : List ℕ) (i : ℕ) :
    (ws.foldr (fun w acc => acc ||| f w) 0).testBit i = ws.any (fun w => (f w).testBit i) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.foldr_cons, Nat.testBit_or, ih, List.any_cons]
    exact Bool.or_comm _ _

def bop (a b : ℕ) : Finset ℕ := {a &&& b, a ||| b}
def uop (a : ℕ) : Finset ℕ := {mask ^^^ a}

def sepOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 != w.testBit pq.2))

def monOK (ws : List ℕ) : Bool :=
  prs.all (fun pq => ws.any (fun w => w.testBit pq.1 && !w.testBit pq.2))

theorem sepF_of {ws : List ℕ} (h : sepOK (prsOf N J) ws = true) : sepF N J ws = true := by
  simp only [sepOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, bne_iff_ne] at h
  simp only [sepF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    revert hd
    cases w.testBit (N + i) <;> cases w.testBit (N + J + i) <;> simp
  · simp [hi]

theorem monF_of {ws : List ℕ} (h : monOK (prsOf N J) ws = true) : monF N J ws = true := by
  simp only [monOK, prsOf, List.all_map, List.all_eq_true, List.mem_range, Function.comp_def,
    List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  simp only [monF, beq_iff_eq]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, maskN_testBit, foldr_or_testBit]
  by_cases hi : i < J
  · obtain ⟨w, hw, hd1, hd2⟩ := h i hi
    simp only [hi, decide_true, Bool.and_true, List.any_eq_true]
    refine ⟨w, hw, ?_⟩
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      maskN_testBit, hd1, hd2]
    simp [hi]
  · simp [hi]

def LS : ℕ → List ℕ → Bool
  | 0, ws => ws == [goal]
  | k + 1, ws => ws == [goal] ||
      (decide (ws.length ≤ k + 2) && sepF N J ws && (ws.length != k + 2 || monF N J ws) &&
        ((pairs ws).any (fun t => [t.1 &&& t.2.1, t.1 ||| t.2.1].any (fun z =>
            !ws.contains z && (keepChoices t.1 t.2.1 t.2.2).any (fun kept => LS k (z :: kept)))) ||
         (singles ws).any (fun t => !ws.contains (mask ^^^ t.1) &&
            [t.2, t.1 :: t.2].any (fun kept => LS k ((mask ^^^ t.1) :: kept)))))

theorem LS_mono : ∀ k ws, LS goal mask N J k ws = true → LS goal mask N J (k + 1) ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws h
    simp only [LS] at h ⊢
    simp [h]
  | succ k ih =>
    intro ws h
    rw [LS] at h
    rw [LS]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      bne_iff_ne] at h ⊢
    rcases h with h | ⟨⟨⟨hl, hs⟩, _⟩, h⟩
    · exact Or.inl h
    · refine Or.inr ⟨⟨⟨by omega, hs⟩, Or.inl (by omega)⟩, ?_⟩
      rcases h with ⟨t, ht, z, hz, hc, kept, hk, hr⟩ | ⟨t, ht, hc, kept, hk, hr⟩
      · exact Or.inl ⟨t, ht, z, hz, hc, kept, hk, ih _ hr⟩
      · exact Or.inr ⟨t, ht, hc, kept, hk, ih _ hr⟩

theorem bop_comm (a b : ℕ) : bop a b = bop b a := by
  simp [bop, Nat.land_comm, Nat.lor_comm, Finset.pair_comm]

def Dpq (pq : ℕ × ℕ) (w : ℕ) : Prop := w.testBit pq.1 ≠ w.testBit pq.2

theorem sep_of_live (hD : ∀ pq ∈ prs, Dpq pq goal)
    (hM : ∀ pq ∈ prs, mask.testBit pq.1 = mask.testBit pq.2)
    {k : ℕ} {ws : List ℕ} (h : live bop (uop mask) goal k ws.toFinset) :
    sepOK prs ws = true := by
  simp only [sepOK, List.all_eq_true, List.any_eq_true, bne_iff_ne]
  intro pq hpq
  obtain ⟨w, hw, hd⟩ := live_separates (Dpq pq) (hD pq hpq)
    (by
      intro a b z hz hdz
      simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
      unfold Dpq at hdz ⊢
      rcases hz with rfl | rfl <;> revert hdz <;>
        simp only [Nat.testBit_and, Nat.testBit_or] <;>
        cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
        cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp)
    (by
      intro a z hz hdz
      simp only [uop, Finset.mem_singleton] at hz
      subst hz
      unfold Dpq at hdz ⊢
      have hm := hM pq hpq
      revert hdz
      simp only [Nat.testBit_xor, hm]
      cases mask.testBit pq.2 <;> cases a.testBit pq.1 <;> cases a.testBit pq.2 <;> simp) h
  exact ⟨w, List.mem_toFinset.mp hw, hd⟩

theorem mon_of_live (hO : ∀ pq ∈ prs, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false)
    {k : ℕ} {ws : List ℕ} (hn : ws.Nodup) (h : live bop (uop mask) goal k ws.toFinset)
    (hc : ws.length = k + 1) : monOK prs ws = true := by
  simp only [monOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  intro pq hpq
  obtain ⟨w, hw, hd⟩ := live_tight (fun w => w.testBit pq.1 = true ∧ w.testBit pq.2 = false)
    (hO pq hpq)
    (by
      intro a b z hz hdz
      simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> revert hdz <;>
        simp only [Nat.testBit_and, Nat.testBit_or] <;>
        cases a.testBit pq.1 <;> cases a.testBit pq.2 <;>
        cases b.testBit pq.1 <;> cases b.testBit pq.2 <;> simp) h
    (by rw [List.toFinset_card_of_nodup hn, hc])
  exact ⟨w, List.mem_toFinset.mp hw, hd⟩

theorem LS_complete (hD : ∀ pq ∈ prsOf N J, Dpq pq goal)
    (hM : ∀ pq ∈ prsOf N J, mask.testBit pq.1 = mask.testBit pq.2)
    (hO : ∀ pq ∈ prsOf N J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) :
    ∀ k (ws : List ℕ), ws.Nodup → live bop (uop mask) goal k ws.toFinset →
      LS goal mask N J k ws = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    simp [LS, singleton_list hn h]
  | succ k ih =>
    intro ws hn h
    have hcard := live_card h
    rw [List.toFinset_card_of_nodup hn] at hcard
    have hsep := sepF_of N J (sep_of_live goal mask (prsOf N J) hD hM h)
    have hmon : (ws.length != k + 2) = true ∨ monF N J ws = true := by
      by_cases hl : ws.length = k + 2
      · exact Or.inr (monF_of N J (mon_of_live goal mask (prsOf N J) hO hn h hl))
      · exact Or.inl (by simp [hl])
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩ |
        ⟨a, ha, z, hz, hout, needed, hs, tail⟩
    · exact LS_mono goal mask N J k ws (ih ws hn skip)
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have hzc : ws.contains z = false := by
        simpa using fun hh => hout (List.mem_toFinset.mpr hh)
      have go {a b : ℕ} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ bop a b) :
          [a &&& b, a ||| b].any (fun z =>
            !ws.contains z && (keepChoices a b r).any (fun kept => LS goal mask N J k (z :: kept)))
            = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live bop (uop mask) goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hrec := ih _ hnd hl
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
        refine ⟨z, ?_, hzc, kept, hk, hrec⟩
        simp only [bop, Finset.mem_insert, Finset.mem_singleton] at hop
        rcases hop with rfl | rfl <;> simp
      simp only [LS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      right
      refine ⟨⟨⟨by omega, hsep⟩, hmon⟩, Or.inl ?_⟩
      simp only [List.any_eq_true]
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, by simpa using go hp hs hz⟩
      · exact ⟨(b, a, r), swap, by
          simpa using go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
            (bop_comm a b ▸ hz)⟩
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      simp only [uop, Finset.mem_singleton] at hz
      subst hz
      have hzc : ws.contains (mask ^^^ a) = false := by
        simpa using fun hh => hout (List.mem_toFinset.mpr hh)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
      have hznew : (mask ^^^ a) ∉ kept := by
        intro hu
        apply hout
        rw [hs]
        exact Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu))
      have hnd : ((mask ^^^ a) :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live bop (uop mask) goal k ((mask ^^^ a) :: kept).toFinset := by
        simpa [hfin] using tail
      have hrec := ih _ hnd hl
      simp only [LS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      right
      refine ⟨⟨⟨by omega, hsep⟩, hmon⟩, Or.inr ?_⟩
      simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨(a, r), hm, hzc, kept, hk, hrec⟩

end Search

section Circ

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def beh (W : List (List Bool)) (i : ℕ) : ℕ := enc (W.map fun w => w.getD i false)

theorem getD_map_row (W : List (List Bool)) (i r : ℕ) :
    (W.map fun w => w.getD i false).getD r false = (W.getD r []).getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[r]? <;> simp

theorem beh_testBit (W : List (List Bool)) (i r : ℕ) :
    (beh W i).testBit r = (W.getD r []).getD i false := by
  rw [beh, testBit_enc, getD_map_row]

theorem row_of_lt {W : List (List Bool)} {r : ℕ} (h : r < W.length) :
    W.getD r [] ∈ W := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem row_of_ge {W : List (List Bool)} {r : ℕ} (h : W.length ≤ r) : W.getD r [] = [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_step_ne {w : List Bool} {g : Gate} {i : ℕ} (hi : i ≠ w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem getD_step_eq {w : List Bool} {g : Gate} :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

theorem mapstep_row (W : List (List Bool)) (g : Gate) (r : ℕ) :
    (W.map (fun w => step w g)).getD r [] =
      if r < W.length then step (W.getD r []) g else [] := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : r < W.length
  · simp [h, List.getElem?_eq_getElem h]
  · simp [h, List.getElem?_eq_none (Nat.le_of_not_lt h)]

theorem beh_old {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) (g : Gate) {i : ℕ}
    (hi : i ≠ L) : beh (W.map (fun w => step w g)) i = beh W i := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    rw [getD_step_ne (by rw [hl _ (row_of_lt h)]; exact hi)]
  · simp only [h, ↓reduceIte]
    rw [row_of_ge (Nat.le_of_not_lt h)]

theorem beh_beyond {W : List (List Bool)} {L : ℕ} (hl : ∀ w ∈ W, w.length = L) {i : ℕ}
    (hi : L ≤ i) : beh W i = 0 := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, Nat.zero_testBit]
  by_cases h : r < W.length
  · have h2 : (W.getD r []).length ≤ i := by rw [hl _ (row_of_lt h)]; exact hi
    exact List.getD_eq_default _ _ h2
  · rw [row_of_ge (Nat.le_of_not_lt h)]
    rfl

def okGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem beh_new {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (g : Gate) (z : ℕ)
    (hz : ∀ r, (r < N → z.testBit r =
        g.op.eval (g.inputs.map fun i => (W.getD r []).getD i false)) ∧
      (N ≤ r → z.testBit r = false)) :
    beh (W.map (fun w => step w g)) L = z := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [beh_testBit, mapstep_row]
  by_cases h : r < W.length
  · simp only [h, ↓reduceIte]
    have hm := row_of_lt h
    have := getD_step_eq (w := W.getD r []) (g := g)
    rw [hl _ hm] at this
    rw [this, (hz r).1 (hN ▸ h)]
  · simp only [h, ↓reduceIte]
    rw [(hz r).2 (by omega)]
    rfl

theorem gate_step {W : List (List Bool)} {L N : ℕ} (hl : ∀ w ∈ W, w.length = L)
    (hN : W.length = N) (av : Finset ℕ) (hmask : maskN N ∈ av) (hinv : ∀ i, beh W i ∈ av)
    (g : Gate) (hg : okGate g) :
    ∃ z, (z ∈ av ∨ (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ z ∈ bop a b) ∨
        (∃ a ∈ av, z ∈ uop (maskN N) a)) ∧
      beh (W.map (fun w => step w g)) L = z := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  have hbeyond := beh_beyond hl (le_refl L)
  have hi : ∀ i r, N ≤ r → (beh W i).testBit r = false := by
    intro i r hr
    rw [beh_testBit, row_of_ge (by omega)]
    rfl
  have hmk : ∀ r, N ≤ r → (maskN N).testBit r = false := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  have hmk' : ∀ r, r < N → (maskN N).testBit r = true := by
    intro r hr
    rw [maskN_testBit]
    simp; omega
  match inputs, hlen with
  | [], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
    · refine ⟨0, Or.inl (hbeyond ▸ hinv L), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [GateOp.eval], fun _ => by simp⟩
    · refine ⟨maskN N, Or.inl hmask, beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [hmk' r hr, GateOp.eval], fun hr => hmk r hr⟩
  | [i], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨beh W i, Or.inl (hinv i), beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun _ => by simp [beh_testBit, GateOp.eval], fun hr => hi i r hr⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | [i, j], _ =>
    rcases hop with rfl | rfl | rfl
    · refine ⟨beh W i &&& beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.and_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_and, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_and, hi i r hr]⟩
    · refine ⟨beh W i ||| beh W j, ?_, beh_new hl hN _ _ ?_⟩
      · by_cases e : beh W i = beh W j
        · left; rw [e, Nat.or_self]; exact hinv j
        · right; left; exact ⟨_, hinv i, _, hinv j, e, by simp [bop]⟩
      · intro r
        exact ⟨fun _ => by simp [Nat.testBit_or, beh_testBit, GateOp.eval],
          fun hr => by simp [Nat.testBit_or, hi i r hr, hi j r hr]⟩
    · refine ⟨maskN N ^^^ beh W i, Or.inr (Or.inr ⟨beh W i, hinv i, by simp [uop]⟩),
        beh_new hl hN _ _ ?_⟩
      intro r
      exact ⟨fun hr => by simp [Nat.testBit_xor, hmk' r hr, beh_testBit, GateOp.eval],
        fun hr => by simp [Nat.testBit_xor, hmk r hr, hi i r hr]⟩
  | _ :: _ :: _ :: _, h => simp at h

def stepAll (gs : List Gate) (W : List (List Bool)) : List (List Bool) :=
  gs.foldl (fun W g => W.map (fun w => step w g)) W

theorem to_build (N goal : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, okGate g) :
    ∀ (L : ℕ) (W : List (List Bool)) (av : Finset ℕ), (∀ w ∈ W, w.length = L) → W.length = N →
      maskN N ∈ av → (∀ i, beh W i ∈ av) → ∀ o, beh (stepAll gs W) o = goal →
      build bop (uop (maskN N)) goal gs.length av := by
  induction gs with
  | nil =>
    intro L W av _ _ _ hinv o ho
    exact ho ▸ hinv o
  | cons g gs ih =>
    intro L W av hl hN hm hinv o ho
    obtain ⟨z, hz, hbz⟩ := gate_step hl hN av hm hinv g (hg g (by simp))
    have hl' : ∀ w ∈ W.map (fun w => step w g), w.length = L + 1 := by
      intro w hw
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
      simp [step, hl w0 hw0]
    have hN' : (W.map (fun w => step w g)).length = N := by simp [hN]
    have hinv' : ∀ i, beh (W.map (fun w => step w g)) i ∈ insert z av := by
      intro i
      by_cases hi : i = L
      · subst hi; rw [hbz]; exact Finset.mem_insert_self _ _
      · rw [beh_old hl g hi]; exact Finset.mem_insert_of_mem (hinv i)
    have hrec := ih (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) (L + 1) _ (insert z av)
      hl' hN' (Finset.mem_insert_of_mem hm) hinv' o ho
    rw [List.length_cons]
    rcases hz with hz | ⟨a, ha, b, hb, hab, hz⟩ | ⟨a, ha, hz⟩
    · rw [Finset.insert_eq_of_mem hz] at hrec; exact Or.inl hrec
    · exact Or.inr (Or.inl ⟨a, ha, b, hb, hab, z, hz, hrec⟩)
    · exact Or.inr (Or.inr ⟨a, ha, z, hz, hrec⟩)

theorem stepAll_eq (gs : List Gate) :
    ∀ W, stepAll gs W = W.map (fun w => gs.foldl step w) := by
  induction gs with
  | nil => intro W; simp [stepAll]
  | cons g gs ih =>
    intro W
    show stepAll gs (W.map (fun w => step w g)) = _
    rw [ih, List.map_map]
    rfl

def rowsOf (n m : ℕ) (ex : List (Fin n × Fin m)) : List (List Bool) :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => oneEach u v) ++
    ex.map (fun p => oneEach p.1 p.2)

def goalOf {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) : List Bool :=
  ((List.finRange n).flatMap fun u => (List.finRange m).map fun v => A u v) ++
    ex.map (fun p => A p.1 p.2)

theorem rows_len (n m : ℕ) (ex : List (Fin n × Fin m)) :
    ∀ w ∈ rowsOf n m ex, w.length = n + m := by
  intro w hw
  simp only [rowsOf, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and] at hw
  rcases hw with ⟨u, v, rfl⟩ | ⟨p, _, rfl⟩ <;> simp [oneEach]

theorem final_beh {n m : ℕ} (A : Fin n → Fin m → Bool) (ex : List (Fin n × Fin m)) (C : Circuit)
    (hr : Represents A C) :
    beh (stepAll C.gates (rowsOf n m ex)) C.output = enc (goalOf A ex) := by
  rw [beh, stepAll_eq, List.map_map]
  congr 1
  have : (rowsOf n m ex).map (fun x => C.eval x) = goalOf A ex := by
    simp only [rowsOf, goalOf, List.map_append, List.map_flatMap, List.map_map]
    congr 1
    · congr 1
      funext u
      apply List.map_congr_left
      intro v _
      exact hr u v
    · apply List.map_congr_left
      intro p _
      exact hr p.1 p.2
  rw [← this]
  rfl

theorem refute {n m : ℕ} (A : Fin n → Fin m → Bool) (K Nb J Nt goal mask : ℕ) (init : List ℕ)
    (ex : List (Fin n × Fin m))
    (hN : (rowsOf n m ex).length = Nt) (hgoal : enc (goalOf A ex) = goal) (hmask : maskN Nt = mask)
    (hinit : ((List.range (n + m)).all (fun i => init.contains (beh (rowsOf n m ex) i)) &&
      init.contains 0 && init.contains mask) = true)
    (hnd : init.Nodup)
    (hprs : (List.range J).all (fun j => (goal.testBit (Nb + j) && !goal.testBit (Nb + J + j)) &&
      (mask.testBit (Nb + j) == mask.testBit (Nb + J + j))) = true)
    (hsearch : init.sublists.all (fun l => !LS goal mask Nb J K l) = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ K ∧ Represents A C := by
  rintro ⟨C, hF, hs, hr⟩
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_range] at hinit
  obtain ⟨⟨hinp, h0⟩, hm⟩ := hinit
  have hinv : ∀ i, beh (rowsOf n m ex) i ∈ init.toFinset := by
    intro i
    rw [List.mem_toFinset]
    by_cases h : i < n + m
    · exact hinp i h
    · rw [beh_beyond (rows_len n m ex) (Nat.le_of_not_lt h)]; exact h0
  have hb := to_build Nt goal C.gates hF (n + m) (rowsOf n m ex) init.toFinset (rows_len n m ex) hN
    (by rw [hmask]; exact List.mem_toFinset.mpr hm) hinv C.output
    (by rw [final_beh A ex C hr, hgoal])
  rw [hmask] at hb
  have hb' := build_mono hb K hs
  obtain ⟨S, hS, hlive⟩ := compress hb'
  have hall : ∀ pq ∈ prsOf Nb J, (goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false) ∧
      mask.testBit pq.1 = mask.testBit pq.2 := by
    intro pq hpq
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hpq
    have := List.all_eq_true.mp hprs j hj
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at this
    exact this
  have hO : ∀ pq ∈ prsOf Nb J, goal.testBit pq.1 = true ∧ goal.testBit pq.2 = false :=
    fun pq hpq => (hall pq hpq).1
  have hD : ∀ pq ∈ prsOf Nb J, Dpq pq goal := by
    intro pq hpq
    have := hO pq hpq
    unfold Dpq
    rw [this.1, this.2]
    simp
  have hM : ∀ pq ∈ prsOf Nb J, mask.testBit pq.1 = mask.testBit pq.2 :=
    fun pq hpq => (hall pq hpq).2
  let l := init.filter (fun x => decide (x ∈ S))
  have hl_sub : l ∈ init.sublists := List.mem_sublists.mpr List.filter_sublist
  have hl_nd : l.Nodup := hnd.filter _
  have hl_fs : l.toFinset = S := by
    ext x
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hS h), h⟩⟩
  have hc := LS_complete goal mask Nb J hD hM hO K l hl_nd (hl_fs ▸ hlive)
  have hf := List.all_eq_true.mp hsearch l hl_sub
  rw [hc] at hf
  exact Bool.noConfusion hf

end Circ

def E0 : List (Fin 5 × Fin 5) := [(2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 1), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (3, 2), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 3), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (4, 4), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2), (0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4), (3, 0), (3, 3), (3, 4), (4, 0), (4, 1), (4, 2)]
def G0 : ℕ := 4611686018419196928 + ((4611686018427387903 + ((1) <<< 62)) <<< 62)
def MK0 : ℕ := (1 <<< 225) - 1
def I0 : List ℕ := [(31 + ((0 + ((2305911178999627838 + ((16252943) <<< 62)) <<< 62)) <<< 62)), (992 + ((0 + ((2181433149884352 + ((520094192) <<< 62)) <<< 62)) <<< 62)), (35184338566144 + ((0 + ((33777029417564160 + ((8053071360) <<< 62)) <<< 62)) <<< 62)), (4611650834056314880 + ((8388607 + ((252201819651145728 + ((60129599488) <<< 62)) <<< 62)) <<< 62)), (32505856 + ((4611686018418999296 + ((2017614557209165825 + ((481036795904) <<< 62)) <<< 62)) <<< 62)), (35184339616801 + ((0 + ((2630175059458949186 + ((77326786576) <<< 62)) <<< 62)) <<< 62)), (4611650834057463874 + ((7 + ((578858239694211204 + ((138010559009) <<< 62)) <<< 62)) <<< 62)), (4329604 + ((8388600 + ((1157716479388422408 + ((276021118018) <<< 62)) <<< 62)) <<< 62)), (8659208 + ((8796084633600 + ((81645413295268368 + ((19465783428) <<< 62)) <<< 62)) <<< 62)), (17318416 + ((4611677222334365696 + ((163290826590536737 + ((38931566856) <<< 62)) <<< 62)) <<< 62)), (0), (4611686018427387903 + ((4611686018427387903 + ((4611686018427387903 + ((549755813887) <<< 62)) <<< 62)) <<< 62))]

theorem C0_0 : ((I0.sublists.drop (1024 * 0)).take 1024).all (fun l => !LS G0 MK0 25 100 6 l) = true := by
  decide +kernel

theorem C0_1 : ((I0.sublists.drop (1024 * 1)).take 1024).all (fun l => !LS G0 MK0 25 100 6 l) = true := by
  decide +kernel

theorem C0_2 : ((I0.sublists.drop (1024 * 2)).take 1024).all (fun l => !LS G0 MK0 25 100 6 l) = true := by
  decide +kernel

theorem C0_3 : ((I0.sublists.drop (1024 * 3)).take 1024).all (fun l => !LS G0 MK0 25 100 6 l) = true := by
  decide +kernel

theorem S0 : I0.sublists.all (fun l => !LS G0 MK0 25 100 6 l) = true :=
  all_of_chunks _ _ 1024 4 (by decide +kernel) (fun i hi => match i, hi with
    | 0, _ => C0_0
    | 1, _ => C0_1
    | 2, _ => C0_2
    | 3, _ => C0_3
    | _ + 4, hi => absurd hi (by omega))

theorem mono_fan {C : Circuit} (h : Monotone2 C) : FanInTwo C := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 ⊢
  tauto

end PEqualNP.Outside.L_meta_26382

theorem PEqualNP.Outside.L_meta_26382 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 1, 6, 24] : List ℕ).getD u.val 0).testBit v.val) C) := by
  exact PEqualNP.Outside.L_meta_26382.refute (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 1, 6, 24] : List ℕ).getD u.val 0).testBit v.val) 6 25 100 225 PEqualNP.Outside.L_meta_26382.G0 PEqualNP.Outside.L_meta_26382.MK0 PEqualNP.Outside.L_meta_26382.I0 PEqualNP.Outside.L_meta_26382.E0
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) PEqualNP.Outside.L_meta_26382.S0
