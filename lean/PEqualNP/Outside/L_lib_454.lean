import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_454 : (∀ (R : Type) [CommSemiring R] (m n : ℕ) (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R),
  (Nat.factorial m : R) * (A * B).permanent =
    ∑ f : Fin m → Fin n,
      (A.submatrix id f).permanent * (B.submatrix f id).permanent) := by
  classical
  intro R _ m n A B
  let term (f : Fin m → Fin n) :=
    (A.submatrix id f).permanent * ∏ i, B (f i) i
  have expand : (A * B).permanent = ∑ f, term f := by
    simp only [term, Matrix.permanent, Matrix.mul_apply, Finset.prod_univ_sum,
      Fintype.piFinset_univ, Matrix.submatrix_apply, id_eq, Finset.sum_mul,
      Finset.prod_mul_distrib]
    rw [Finset.sum_comm]
  have reorder (t : Equiv.Perm (Fin m)) :
      (∑ f : Fin m → Fin n, (A.submatrix id f).permanent * ∏ i, B (f (t i)) i) =
        (A * B).permanent := by
    rw [expand]
    let e := t.symm.arrowCongr (Equiv.refl (Fin n))
    apply Fintype.sum_equiv e
    intro f
    change (A.submatrix id f).permanent * _ =
      ((A.submatrix id f).submatrix id t).permanent * _
    rw [Matrix.permanent_permute_rows]
    rfl
  symm
  simp only [Matrix.permanent, Matrix.submatrix_apply, id_eq] at reorder ⊢
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [reorder]
  simp [Fintype.card_perm, nsmul_eq_mul, Finset.mul_sum]
