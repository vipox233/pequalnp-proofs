import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_475_aux

private lemma card_max_on {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    S.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let fiber : Fin n → Finset (Equiv.Perm (Fin n)) := fun a =>
    (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun π => ∀ j ∈ S, j ≠ a → (π j).val < (π a).val)
  have hcard_eq : ∀ a ∈ S, (fiber a).card = (fiber i).card := by
    intro a _ha
    refine Finset.card_bij (fun π _ => π * Equiv.swap a i) ?_ ?_ ?_
    · intro π hπ
      simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      intro j hjS hji
      change (π (Equiv.swap a i j)).val < (π (Equiv.swap a i i)).val
      rw [Equiv.swap_apply_right]
      by_cases hja : j = a
      · subst hja
        rw [Equiv.swap_apply_left]
        exact hπ i hi (Ne.symm hji)
      · rw [Equiv.swap_apply_of_ne_of_ne hja hji]
        exact hπ j hjS hja
    · intro π₁ _ π₂ _ h
      exact mul_right_cancel h
    · intro σ hσ
      refine ⟨σ * Equiv.swap a i, ?_, ?_⟩
      · simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
        intro j hjS hja
        change (σ (Equiv.swap a i j)).val < (σ (Equiv.swap a i a)).val
        rw [Equiv.swap_apply_left]
        by_cases hji : j = i
        · subst hji
          rw [Equiv.swap_apply_right]
          exact hσ a _ha hja.symm
        · rw [Equiv.swap_apply_of_ne_of_ne hja hji]
          exact hσ j hjS hji
      · rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  have hdisj : Set.PairwiseDisjoint (S : Set (Fin n)) fiber := by
    intro a ha b hb hab
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π hπa hπb
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hπa hπb
    have h1 := hπa b hb hab.symm
    have h2 := hπb a ha hab
    omega
  have hunion : S.biUnion fiber = Finset.univ := by
    ext π
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    obtain ⟨a, haS, hmax⟩ := Finset.exists_max_image S (fun j => (π j).val) ⟨i, hi⟩
    refine ⟨a, haS, ?_⟩
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hjS hja
    have hle := hmax j hjS
    have hne : (π j).val ≠ (π a).val := fun heq => hja (π.injective (Fin.ext heq))
    omega
  have htot : (S.biUnion fiber).card = Fintype.card (Equiv.Perm (Fin n)) := by
    rw [hunion, Finset.card_univ]
  rw [Finset.card_biUnion hdisj] at htot
  rw [Finset.sum_congr rfl hcard_eq, Finset.sum_const, smul_eq_mul] at htot
  exact htot

private theorem main_aux : ∀ n : Nat,
    let V := Fin n
    let Point := V → Bool
    let Clause := Finset (V × Bool)
    let sat := fun (formula : Finset Clause) (x : Point) =>
      ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
    let Order := Equiv.Perm V
    ∀ F : Finset Clause,
      let forced := fun (s : Point) (order : Order) =>
        (Finset.univ : Finset V).filter (fun i =>
          ∃ c ∈ F, (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨
            ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))
      let critical := fun (s : Point) (i : V) (c : Clause) =>
        c ∈ F ∧ (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨ (e.1 ≠ i ∧ s e.1 ≠ e.2)
      ∀ (s : Point) (I : Finset V) (witness : V → Clause),
        sat F s → (∀ i ∈ I, critical s i (witness i)) →
        ((Fintype.card Order : ℚ) * I.sum (fun dir => ((witness dir).card : ℚ)⁻¹)) ≤
          (Finset.univ : Finset Order).sum (fun perm => ((forced s perm).card : ℚ)) := by
  intro n
  dsimp only
  intro F s I witness _hsat hcrit
  let Order := Equiv.Perm (Fin n)
  let forced : Order → Finset (Fin n) := fun order =>
    (Finset.univ : Finset (Fin n)).filter (fun i =>
      ∃ c ∈ F, (i, s i) ∈ c ∧ ∀ e ∈ c, e = (i, s i) ∨
        ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))
  have hswap : (Finset.univ : Finset Order).sum (fun perm => (forced perm).card) =
      (Finset.univ : Finset (Fin n)).sum (fun i =>
        ((Finset.univ : Finset Order).filter (fun perm => i ∈ forced perm)).card) := by
    have h1 : ∀ perm : Order, (forced perm).card =
        (Finset.univ : Finset (Fin n)).sum (fun i => if i ∈ forced perm then 1 else 0) := by
      intro perm
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext i
      simp
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  change ((Fintype.card Order : ℚ) * I.sum (fun dir => ((witness dir).card : ℚ)⁻¹)) ≤
    (Finset.univ : Finset Order).sum (fun perm => ((forced perm).card : ℚ))
  rw [← Nat.cast_sum, hswap, Nat.cast_sum]
  calc (Fintype.card Order : ℚ) * I.sum (fun dir => ((witness dir).card : ℚ)⁻¹)
      = I.sum (fun i => (Fintype.card Order : ℚ) * ((witness i).card : ℚ)⁻¹) := by
        rw [Finset.mul_sum]
    _ ≤ I.sum (fun i => (((Finset.univ : Finset Order).filter (fun perm => i ∈ forced perm)).card : ℚ)) := by
        refine Finset.sum_le_sum fun i hiI => ?_
        obtain ⟨hcF, hi_mem, hrest⟩ := hcrit i hiI
        let c := witness i
        let S : Finset (Fin n) := c.image Prod.fst
        have hiS : i ∈ S := Finset.mem_image.mpr ⟨(i, s i), hi_mem, rfl⟩
        have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
        have hS_le : S.card ≤ c.card := Finset.card_image_le
        have hmax := card_max_on S i hiS
        have hsub : (Finset.univ : Finset Order).filter
            (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val) ⊆
            (Finset.univ : Finset Order).filter (fun perm => i ∈ forced perm) := by
          intro π hπ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
          simp only [forced, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨c, hcF, hi_mem, fun e he => ?_⟩
          rcases hrest e he with rfl | ⟨hne, hval⟩
          · exact Or.inl rfl
          · refine Or.inr ⟨hπ e.1 (Finset.mem_image.mpr ⟨e, he, rfl⟩) hne, hval⟩
        have hcard_le : ((Finset.univ : Finset Order).filter
            (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card ≤
            ((Finset.univ : Finset Order).filter (fun perm => i ∈ forced perm)).card :=
          Finset.card_le_card hsub
        have hS_pos_q : (0 : ℚ) < (S.card : ℚ) := Nat.cast_pos.mpr hS_pos
        have hc_pos_q : (0 : ℚ) < (c.card : ℚ) := Nat.cast_pos.mpr (lt_of_lt_of_le hS_pos hS_le)
        have hmax_q : (S.card : ℚ) * (((Finset.univ : Finset Order).filter
            (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card : ℚ) =
            (Fintype.card Order : ℚ) := by
          exact_mod_cast hmax
        have heq_inv : (Fintype.card Order : ℚ) * (S.card : ℚ)⁻¹ =
            (((Finset.univ : Finset Order).filter
              (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card : ℚ) := by
          rw [← hmax_q, mul_comm (S.card : ℚ), mul_assoc, mul_inv_cancel₀ (ne_of_gt hS_pos_q), mul_one]
        have hinv_le : (c.card : ℚ)⁻¹ ≤ (S.card : ℚ)⁻¹ := by
          exact inv_anti₀ hS_pos_q (Nat.cast_le.mpr hS_le)
        calc (Fintype.card Order : ℚ) * (c.card : ℚ)⁻¹
            ≤ (Fintype.card Order : ℚ) * (S.card : ℚ)⁻¹ := by
              exact mul_le_mul_of_nonneg_left hinv_le (Nat.cast_nonneg _)
          _ = (((Finset.univ : Finset Order).filter
                (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card : ℚ) := heq_inv
          _ ≤ (((Finset.univ : Finset Order).filter (fun perm => i ∈ forced perm)).card : ℚ) := by
              exact Nat.cast_le.mpr hcard_le
    _ ≤ (Finset.univ : Finset (Fin n)).sum (fun i =>
          (((Finset.univ : Finset Order).filter (fun perm => i ∈ forced perm)).card : ℚ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (fun _ _ _ => Nat.cast_nonneg _)

end PEqualNP.Outside.L_lib_475_aux

theorem PEqualNP.Outside.L_lib_475 : (∀ n : Nat,
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  let Order := Equiv.Perm V
  ∀ F : Finset Clause,
    let forced := fun (s : Point) (order : Order) =>
      (Finset.univ : Finset V).filter (fun i =>
        ∃ c ∈ F, (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨
          ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))
    let critical := fun (s : Point) (i : V) (c : Clause) =>
      c ∈ F ∧ (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨ (e.1 ≠ i ∧ s e.1 ≠ e.2)
    ∀ (s : Point) (I : Finset V) (witness : V → Clause),
      sat F s → (∀ i ∈ I, critical s i (witness i)) →
      ((Fintype.card Order : ℚ) * I.sum (fun dir => ((witness dir).card : ℚ)⁻¹)) ≤
        (Finset.univ : Finset Order).sum (fun perm => ((forced s perm).card : ℚ))) :=
  PEqualNP.Outside.L_lib_475_aux.main_aux
