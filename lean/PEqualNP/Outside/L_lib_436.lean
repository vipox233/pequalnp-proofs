import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_436_aux

open Finset

theorem sum_superset_alt (n : ℕ) (T : Finset (Fin n)) :
    ∑ S : Finset (Fin n), (if T ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) =
      if T = Finset.univ then 1 else 0 := by
  by_cases hT : T = Finset.univ
  · subst hT
    rw [if_pos rfl, Finset.sum_eq_single Finset.univ]
    · simp [Fintype.card_fin]
    · intro S _ hS
      have hns : ¬ (Finset.univ ⊆ S) := fun h =>
        hS (Finset.Subset.antisymm (Finset.subset_univ S) h)
      rw [if_neg hns]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hT]
    obtain ⟨a, ha⟩ : ∃ a : Fin n, a ∉ T := by
      by_contra hc
      apply hT
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hnx
      exact hc ⟨x, hnx⟩
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun S : Finset (Fin n) => a ∈ S)]
    have hbij :
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => a ∈ S),
          (if T ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => a ∉ S),
          - (if T ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) := by
      symm
      refine Finset.sum_nbij' (fun S => insert a S) (fun S => S.erase a)
        ?_ ?_ ?_ ?_ ?_
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        exact Finset.mem_insert_self a S
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
        exact Finset.notMem_erase a S
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        exact Finset.erase_insert hS
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        exact Finset.insert_erase hS
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        have hsub_iff : T ⊆ insert a S ↔ T ⊆ S := by
          constructor
          · intro h x hx
            rcases Finset.mem_insert.1 (h hx) with rfl | hxS
            · exact absurd hx ha
            · exact hxS
          · intro h x hx
            exact Finset.mem_insert_of_mem (h hx)
        by_cases hTS : T ⊆ S
        · rw [if_pos hTS, if_pos (hsub_iff.2 hTS)]
          have hcard : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem hS
          have hle : (insert a S).card ≤ n := by
            have h1 := Finset.card_le_card (Finset.subset_univ (insert a S))
            rw [Finset.card_univ, Fintype.card_fin] at h1
            exact h1
          have hexp : n - S.card = (n - (insert a S).card) + 1 := by omega
          rw [hexp, pow_succ]
          ring
        · rw [if_neg hTS, if_neg (fun h => hTS (hsub_iff.1 h)), neg_zero]
    rw [hbij, Finset.sum_neg_distrib, neg_add_cancel]

theorem image_eq_univ_iff_bijective {n : ℕ} (f : Fin n → Fin n) :
    Finset.univ.image f = Finset.univ ↔ Function.Bijective f := by
  have hsurj : Finset.univ.image f = Finset.univ ↔ Function.Surjective f := by
    constructor
    · intro h y
      have hy : y ∈ Finset.univ.image f := by
        rw [h]
        exact Finset.mem_univ y
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hy
      exact ⟨x, rfl⟩
    · intro h
      ext y
      simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
      exact h y
  rw [hsurj]
  exact ⟨fun hs => ⟨Finite.injective_iff_surjective.2 hs, hs⟩, fun hb => hb.2⟩

theorem main (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) :
    M.permanent = ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - S.card) *
      ∏ i : Fin n, ∑ j ∈ S, M i j := by
  have hprod : ∀ S : Finset (Fin n),
      ∏ i : Fin n, ∑ j ∈ S, M i j =
      ∑ f : Fin n → Fin n, if Finset.univ.image f ⊆ S then ∏ i : Fin n, M i (f i) else 0 := by
    intro S
    have hrow : ∀ i : Fin n, ∑ j ∈ S, M i j = ∑ j : Fin n, if j ∈ S then M i j else 0 := by
      intro i
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext j
      simp
    simp_rw [hrow]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    by_cases hf : Finset.univ.image f ⊆ S
    · rw [if_pos hf]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have hi : f i ∈ S := hf (Finset.mem_image.2 ⟨i, Finset.mem_univ i, rfl⟩)
      rw [if_pos hi]
    · rw [if_neg hf]
      obtain ⟨i, hi⟩ : ∃ i : Fin n, f i ∉ S := by
        by_contra hc
        apply hf
        intro y hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
        by_contra hni
        exact hc ⟨i, hni⟩
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have hrhs :
      ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - S.card) * ∏ i : Fin n, ∑ j ∈ S, M i j =
      ∑ f ∈ Finset.univ.filter (fun f : Fin n → Fin n => Finset.univ.image f = Finset.univ),
        ∏ i : Fin n, M i (f i) := by
    simp_rw [hprod, Finset.mul_sum]
    rw [Finset.sum_comm]
    have hinner : ∀ f : Fin n → Fin n,
        ∑ S : Finset (Fin n), (-1 : ℤ) ^ (n - S.card) *
          (if Finset.univ.image f ⊆ S then ∏ i : Fin n, M i (f i) else 0) =
        if Finset.univ.image f = Finset.univ then ∏ i : Fin n, M i (f i) else 0 := by
      intro f
      have hterm : ∀ S : Finset (Fin n),
          (-1 : ℤ) ^ (n - S.card) *
            (if Finset.univ.image f ⊆ S then ∏ i : Fin n, M i (f i) else 0) =
          (if Finset.univ.image f ⊆ S then (-1 : ℤ) ^ (n - S.card) else 0) *
            ∏ i : Fin n, M i (f i) := by
        intro S
        by_cases hS : Finset.univ.image f ⊆ S <;> simp [hS]
      simp_rw [hterm]
      rw [← Finset.sum_mul, sum_superset_alt]
      by_cases hf : Finset.univ.image f = Finset.univ <;> simp [hf]
    simp_rw [hinner]
    rw [← Finset.sum_filter]
  rw [hrhs, Matrix.permanent]
  refine Finset.sum_nbij' (fun σ : Equiv.Perm (Fin n) => (σ.symm : Fin n → Fin n))
    (fun f => by
      classical
      exact if hf : Function.Bijective f then (Equiv.ofBijective f hf).symm else 1)
    ?_ ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (image_eq_univ_iff_bijective σ.symm).2 σ.symm.bijective
  · intro _ _
    exact Finset.mem_univ _
  · intro σ _
    have hbij : Function.Bijective (σ.symm : Fin n → Fin n) := σ.symm.bijective
    simp only [hbij, ↓reduceDIte]
    ext i
    simp
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hbij : Function.Bijective f := (image_eq_univ_iff_bijective f).1 hf
    simp only [hbij, ↓reduceDIte]
    ext i
    simp
  · intro σ _
    have hcomp := Equiv.prod_comp σ (fun i => M i (σ.symm i))
    simp only [Equiv.symm_apply_apply] at hcomp
    exact hcomp

end PEqualNP.Outside.L_lib_436_aux

theorem PEqualNP.Outside.L_lib_436 :
∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ),
  M.permanent = ∑ S : Finset (Fin n), (-1 : ℤ)^(n-S.card) *
    ∏ i : Fin n, ∑ j ∈ S, M i j := by
  intro n M
  exact PEqualNP.Outside.L_lib_436_aux.main n M
