import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_770 : ∀ (k : ℕ) (c a : Fin k → ℝ), Function.Injective a →
  (∀ x : Fin k, (∑ i, c i * (a i) ^ (x : ℕ)) = 0) → ∀ i, c i = 0 := by
  intro k c a ha h
  have hd : (Matrix.vandermonde a).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr ha
  have hv : (Matrix.vandermonde a).transpose.mulVec c = 0 := by
    funext x
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply, Pi.zero_apply]
    rw [← h x]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have := Matrix.eq_zero_of_mulVec_eq_zero hd hv
  intro i
  simp [this]
