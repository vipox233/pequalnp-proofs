import Mathlib

namespace PEqualNP.Outside.L_lib_610_aux

variable {V : Type} [DecidableEq V] [Fintype V]

def rs (U A : Finset V) (w : V → Bool) : V → Bool := fun v => if v ∈ U then decide (v ∈ A) else w v

def ev (T : Finset (Finset V)) (w : V → Bool) : Bool :=
  (((T.filter (fun f => ∀ v ∈ f, w v = true)).card % 2) == 1)

def tg (u : V) (A : Finset V) : Finset V := if u ∈ A then A.erase u else insert u A

theorem tg_tg (u : V) (A : Finset V) : tg u (tg u A) = A := by
  unfold tg
  by_cases h : u ∈ A
  · simp [h, Finset.insert_erase h]
  · simp [h, Finset.erase_insert h]

theorem tg_ne (u : V) (A : Finset V) : tg u A ≠ A := by
  unfold tg
  by_cases h : u ∈ A
  · simp only [h, if_true]
    intro he
    have : u ∈ A.erase u := by rw [he]; exact h
    simp at this
  · simp only [h, if_false]
    intro he
    have : u ∈ insert u A := Finset.mem_insert_self u A
    rw [he] at this
    exact h this

theorem tg_mem_iff (u : V) (A : Finset V) (v : V) (hv : v ≠ u) : v ∈ tg u A ↔ v ∈ A := by
  unfold tg
  split_ifs <;> simp [hv]

theorem tg_sub (U : Finset V) (u : V) (hu : u ∈ U) (A : Finset V) (hA : A ⊆ U) : tg u A ⊆ U := by
  unfold tg
  split_ifs
  · exact (Finset.erase_subset u A).trans hA
  · exact Finset.insert_subset hu hA

theorem natcast_two (n : ℕ) : ((n : ZMod 2)) = if n % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem inner_count (U f : Finset V) (w : V → Bool) (hmax : U ⊆ f → f = U) :
    (∑ A ∈ U.powerset, (if ∀ v ∈ f, rs U A w v = true then (1 : ZMod 2) else 0)) =
      if f = U then 1 else 0 := by
  by_cases hfU : f = U
  · subst hfU
    rw [if_pos rfl, Finset.sum_eq_single f]
    · rw [if_pos]
      intro v hv
      simp [rs, hv]
    · intro A hA hne
      rw [if_neg]
      intro h
      apply hne
      apply Finset.Subset.antisymm (Finset.mem_powerset.mp hA)
      intro v hv
      have := h v hv
      simpa [rs, hv] using this
    · intro h
      exact absurd (Finset.mem_powerset_self f) h
  · rw [if_neg hfU]
    have hU : ¬ U ⊆ f := fun h => hfU (hmax h)
    obtain ⟨u, huU, huf⟩ := Finset.not_subset.mp hU
    refine Finset.sum_involution (fun A _ => tg u A) ?_ ?_ ?_ ?_
    · intro A _
      have hc : (∀ v ∈ f, rs U (tg u A) w v = true) ↔ (∀ v ∈ f, rs U A w v = true) := by
        apply forall_congr'
        intro v
        apply imp_congr_right
        intro hv
        have hvu : v ≠ u := fun h => huf (h ▸ hv)
        simp only [rs, tg_mem_iff u A v hvu]
      simp only [hc]
      split_ifs <;> decide
    · intro A _ _
      exact tg_ne u A
    · intro A hA
      exact Finset.mem_powerset.mpr (tg_sub U u huU A (Finset.mem_powerset.mp hA))
    · intro A _
      exact tg_tg u A

theorem part1 (T : Finset (Finset V)) (U : Finset V) (hU : U ∈ T) (hmax : ∀ f ∈ T, U ⊆ f → f = U)
    (w : V → Bool) : (U.powerset.filter (fun A => ev T (rs U A w) = true)).card % 2 = 1 := by
  have key : (((U.powerset.filter (fun A => ev T (rs U A w) = true)).card : ℕ) : ZMod 2) = 1 := by
    rw [Finset.card_filter, Nat.cast_sum]
    have h1 : ∀ A ∈ U.powerset, (((if ev T (rs U A w) = true then 1 else 0 : ℕ)) : ZMod 2) =
        ∑ f ∈ T, (if ∀ v ∈ f, rs U A w v = true then (1 : ZMod 2) else 0) := by
      intro A _
      have e1 : (((T.filter (fun f => ∀ v ∈ f, rs U A w v = true)).card : ℕ) : ZMod 2) =
          ∑ f ∈ T, (if ∀ v ∈ f, rs U A w v = true then (1 : ZMod 2) else 0) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl (fun f _ => ?_)
        split_ifs <;> simp
      rw [← e1, natcast_two ((T.filter (fun f => ∀ v ∈ f, rs U A w v = true)).card)]
      by_cases h : (T.filter (fun f => ∀ v ∈ f, rs U A w v = true)).card % 2 = 1 <;> simp [ev, h]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun f hf => inner_count U f w (hmax f hf))]
    rw [Finset.sum_ite_eq' T U, if_pos hU]
  have := natcast_two ((U.powerset.filter (fun A => ev T (rs U A w) = true)).card)
  rw [key] at this
  split_ifs at this with h
  · exact h
  · exact absurd this (by decide)

theorem part2 (m r : ℕ) (T : Finset (Finset (Fin m × Fin r))) (U : Finset (Fin m × Fin r)) (hU : U ∈ T)
    (hmax : ∀ f ∈ T, U ⊆ f → f = U) (K : ℕ) (bad : Fin K → Fin m → (Fin r → Bool)) :
    ((Finset.univ : Finset (Fin m × Fin r → Bool)).filter (fun word =>
        ∀ a, ∃ i, i ∉ U.image Prod.fst ∧ (fun v => word (i,v)) = bad a i)).card ≤
      2 ^ U.card * (((Finset.univ : Finset (Fin m × Fin r → Bool)).filter (fun x => ev T x = true)).filter
        (fun word => ∀ a, ∃ i, i ∉ (∅ : Finset (Fin m)) ∧ (fun v => word (i,v)) = bad a i)).card := by
  have hex : ∀ x : Fin m × Fin r → Bool, ∃ A, A ∈ U.powerset ∧ ev T (rs U A x) = true := by
    intro x
    have h := part1 T U hU hmax x
    have hpos : 0 < (U.powerset.filter (fun A => ev T (rs U A x) = true)).card := by omega
    obtain ⟨A, hA⟩ := Finset.card_pos.mp hpos
    exact ⟨A, (Finset.mem_filter.mp hA).1, (Finset.mem_filter.mp hA).2⟩
  choose A hA using hex
  set M := (Finset.univ : Finset (Fin m × Fin r → Bool)).filter (fun word =>
        ∀ a, ∃ i, i ∉ U.image Prod.fst ∧ (fun v => word (i,v)) = bad a i) with hM
  let g : (Fin m × Fin r → Bool) → (Fin m × Fin r → Bool) := fun x => rs U (A x) x
  have h1 := Finset.card_le_mul_card_image M (f := g) (2 ^ U.card) (by
    intro y _
    calc (M.filter (fun x => g x = y)).card ≤ (U.powerset.image (fun B => rs U B y)).card := by
          apply Finset.card_le_card
          intro x hx
          have hgx := (Finset.mem_filter.mp hx).2
          refine Finset.mem_image.mpr ⟨U.filter (fun v => x v = true), Finset.mem_powerset.mpr
            (Finset.filter_subset _ _), ?_⟩
          funext v
          by_cases hv : v ∈ U
          · simp [rs, hv]
          · rw [← hgx]
            simp [rs, g, hv]
      _ ≤ U.powerset.card := Finset.card_image_le
      _ = 2 ^ U.card := Finset.card_powerset U)
  refine le_trans h1 (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hxm := (Finset.mem_filter.mp hx).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hA x).2⟩, ?_⟩
  intro a
  obtain ⟨i, hi, hb⟩ := hxm a
  refine ⟨i, Finset.notMem_empty i, ?_⟩
  rw [← hb]
  funext v
  have hiv : (i, v) ∉ U := fun h => hi (Finset.mem_image.mpr ⟨(i, v), h, rfl⟩)
  simp [g, rs, hiv]

end PEqualNP.Outside.L_lib_610_aux

theorem PEqualNP.Outside.L_lib_610 : ∀ (m r : Nat),
  let V := Fin m × Fin r
  let W := V → Bool
  let Symbol := Fin r → Bool
  let eval := fun (T : Finset (Finset V)) (w : W) =>
    (((T.filter (fun f => ∀ v ∈ f, w v = true)).card % 2) == 1)
  ∀ (terms : Finset (Finset V)) (U : Finset V), U ∈ terms →
    (∀ f ∈ terms, U ⊆ f → f = U) →
    let old := (Finset.univ : Finset W).filter (fun x => eval terms x = true)
    (∀ w : W, (U.powerset.filter (fun A =>
      eval terms (fun v => if v ∈ U then decide (v ∈ A) else w v) = true)).card % 2 = 1) ∧
    ∀ (K : Nat) (bad : Fin K → Fin m → Symbol),
      let gone := U.image Prod.fst
      let miss := fun (J : Finset (Fin m)) (word : W) =>
        ∀ a, ∃ i, i ∉ J ∧ (fun v => word (i,v)) = bad a i
      ((Finset.univ : Finset W).filter (miss gone)).card ≤
        2^U.card * (old.filter (miss ∅)).card := by
  intro m r V W Symbol eval terms U hU hmax old
  exact ⟨fun w => PEqualNP.Outside.L_lib_610_aux.part1 terms U hU hmax w,
    fun K bad => PEqualNP.Outside.L_lib_610_aux.part2 m r terms U hU hmax K bad⟩
