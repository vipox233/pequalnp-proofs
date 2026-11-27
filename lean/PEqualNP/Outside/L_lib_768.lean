import PEqualNP.Defs
import Mathlib.Analysis.InnerProductSpace.Orientation

theorem PEqualNP.Outside.L_lib_768 :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.det ^ 2 ≤ ∏ i, ∑ j, (A i j) ^ 2 := by
  intro n A
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let rows : Fin n → EuclideanSpace ℝ (Fin n) := fun i => WithLp.toLp 2 (A i)
  have hdet : b.toBasis.det rows = A.det := by
    rw [Module.Basis.det_apply]
    have hmatrix : b.toBasis.toMatrix rows = A.transpose := by
      ext i j
      rfl
    rw [hmatrix, Matrix.det_transpose]
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨finrank_euclideanSpace_fin⟩
  let o := b.toBasis.orientation
  have habs := o.abs_volumeForm_apply_le rows
  rw [o.volumeForm_robust' b rows, hdet] at habs
  calc
    A.det ^ 2 = |A.det| ^ 2 := (sq_abs _).symm
    _ ≤ (∏ i, ‖rows i‖) ^ 2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
    _ = ∏ i, ∑ j, (A i j) ^ 2 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => EuclideanSpace.real_norm_sq_eq (rows i)

