import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Rank

theorem PEqualNP.Outside.L_lib_434 : ∀ n : ℕ,
  let D : Matrix (Finset (Fin n)) (Finset (Fin n)) ℚ :=
    fun S T => if Disjoint S T then 1 else 0
  D.rank = 2 ^ n := by
  intro n D
  have hinj : Function.Injective D.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hzero : ∀ U : Finset (Fin n), ∑ T ∈ U.powerset, v T = 0 := by
      intro U
      have hU : D.mulVec v Uᶜ = 0 := congrFun (LinearMap.mem_ker.mp hv) Uᶜ
      rw [Matrix.mulVec] at hU
      simp only [dotProduct, D, ite_mul, one_mul, zero_mul, ← Finset.sum_filter] at hU
      have hfilt : Finset.univ.filter (fun T : Finset (Fin n) => Disjoint Uᶜ T) = U.powerset := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset,
          Finset.disjoint_left, Finset.mem_compl]
        constructor
        · intro h x hxT
          by_contra hxU
          exact h hxU hxT
        · intro h x hxU hxT
          exact hxU (h hxT)
      rwa [hfilt] at hU
    funext U
    induction hcard : U.card using Nat.strong_induction_on generalizing U with
    | ind m ih =>
      have hsum := hzero U
      have hmem : U ∈ U.powerset := Finset.mem_powerset.mpr (Finset.Subset.refl U)
      rw [← Finset.add_sum_erase _ _ hmem] at hsum
      have herase : ∑ T ∈ U.powerset.erase U, v T = 0 := by
        apply Finset.sum_eq_zero
        intro T hT
        have hsub : T ⊆ U := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hT)
        have hne : T ≠ U := Finset.ne_of_mem_erase hT
        have hss : T ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
        have hlt : T.card < m := by rw [← hcard]; exact Finset.card_lt_card hss
        exact ih T.card hlt T rfl
      rw [herase, add_zero] at hsum
      exact hsum
  have hrk : D.rank = Module.finrank ℚ (Finset (Fin n) → ℚ) := by
    unfold Matrix.rank
    exact LinearMap.finrank_range_of_inj hinj
  rw [hrk, Module.finrank_pi, Fintype.card_finset, Fintype.card_fin]
