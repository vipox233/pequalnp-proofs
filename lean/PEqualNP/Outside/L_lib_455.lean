import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_455

private lemma gram_permanent_identity (m n : ℕ) (A B : Matrix (Fin n) (Fin m) ℝ) :
    (m.factorial : ℝ) * (A.transpose * B).permanent =
      ∑ f : Fin m → Fin n, (A.submatrix f id).permanent * (B.submatrix f id).permanent := by
  have hinner : ∀ σ τ : Equiv.Perm (Fin m),
      ∑ f : Fin m → Fin n,
        (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i) =
      ∏ i : Fin m, (A.transpose * B) ((σ⁻¹ * τ) i) i := by
    intro σ τ
    have hprod : ∀ f : Fin m → Fin n,
        (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i) =
        ∏ j : Fin m, (A (f j) (σ⁻¹ j) * B (f j) (τ⁻¹ j)) := by
      intro f
      have hA : (∏ i : Fin m, A (f (σ i)) i) = ∏ j : Fin m, A (f j) (σ⁻¹ j) := by
        simpa using Equiv.prod_comp σ (fun j : Fin m => A (f j) (σ⁻¹ j))
      have hB : (∏ i : Fin m, B (f (τ i)) i) = ∏ j : Fin m, B (f j) (τ⁻¹ j) := by
        simpa using Equiv.prod_comp τ (fun j : Fin m => B (f j) (τ⁻¹ j))
      rw [hA, hB, ← Finset.prod_mul_distrib]
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun (j : Fin m) (k : Fin n) => A k (σ⁻¹ j) * B k (τ⁻¹ j))]
    have hmul : ∀ j : Fin m,
        (∑ k : Fin n, A k (σ⁻¹ j) * B k (τ⁻¹ j)) = (A.transpose * B) (σ⁻¹ j) (τ⁻¹ j) := by
      intro j
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    simp_rw [hmul]
    simpa [Equiv.Perm.mul_apply] using
      (Equiv.prod_comp τ (fun j : Fin m => (A.transpose * B) (σ⁻¹ j) (τ⁻¹ j))).symm
  calc
    (m.factorial : ℝ) * (A.transpose * B).permanent
        = ∑ _σ : Equiv.Perm (Fin m), (A.transpose * B).permanent := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
          ∏ i : Fin m, (A.transpose * B) ((σ⁻¹ * τ) i) i := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [Matrix.permanent]
          exact (Equiv.sum_comp (Equiv.mulLeft σ⁻¹)
            (fun ρ : Equiv.Perm (Fin m) => ∏ i : Fin m, (A.transpose * B) (ρ i) i)).symm
    _ = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m), ∑ f : Fin m → Fin n,
          (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i) := by
          refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => (hinner σ τ).symm
    _ = ∑ f : Fin m → Fin n, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
          (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i) := by
          calc
            ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m), ∑ f : Fin m → Fin n,
                (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i)
                = ∑ σ : Equiv.Perm (Fin m), ∑ f : Fin m → Fin n, ∑ τ : Equiv.Perm (Fin m),
                    (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i) :=
                  Finset.sum_congr rfl fun _ _ => Finset.sum_comm
            _ = ∑ f : Fin m → Fin n, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
                    (∏ i : Fin m, A (f (σ i)) i) * (∏ i : Fin m, B (f (τ i)) i) :=
                  Finset.sum_comm
    _ = ∑ f : Fin m → Fin n, (A.submatrix f id).permanent * (B.submatrix f id).permanent := by
          refine Finset.sum_congr rfl fun f _ => ?_
          simp only [Matrix.permanent, Matrix.submatrix_apply, id_eq, Finset.sum_mul_sum]

end PEqualNP.Outside.L_lib_455

theorem PEqualNP.Outside.L_lib_455 :
    ∀ (m n : ℕ) (A B : Matrix (Fin n) (Fin m) ℝ),
      (A.transpose * B).permanent ^ 2 ≤
        (A.transpose * A).permanent * (B.transpose * B).permanent := by
  intro m n A B
  have hAB := PEqualNP.Outside.L_lib_455.gram_permanent_identity m n A B
  have hAA := PEqualNP.Outside.L_lib_455.gram_permanent_identity m n A A
  have hBB := PEqualNP.Outside.L_lib_455.gram_permanent_identity m n B B
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m → Fin n))
    (fun f => (A.submatrix f id).permanent) (fun f => (B.submatrix f id).permanent)
  simp_rw [sq] at hcs
  rw [← hAB, ← hAA, ← hBB] at hcs
  have hpos : (0 : ℝ) < ((m.factorial : ℝ) * (m.factorial : ℝ)) := by
    have hm : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
    exact mul_pos hm hm
  have hmul :
      ((m.factorial : ℝ) * (m.factorial : ℝ)) * ((A.transpose * B).permanent ^ 2) ≤
      ((m.factorial : ℝ) * (m.factorial : ℝ)) *
        ((A.transpose * A).permanent * (B.transpose * B).permanent) := by
    have hl :
        ((m.factorial : ℝ) * (m.factorial : ℝ)) * ((A.transpose * B).permanent ^ 2) =
        ((m.factorial : ℝ) * (A.transpose * B).permanent) *
          ((m.factorial : ℝ) * (A.transpose * B).permanent) := by ring
    have hr :
        ((m.factorial : ℝ) * (m.factorial : ℝ)) *
          ((A.transpose * A).permanent * (B.transpose * B).permanent) =
        ((m.factorial : ℝ) * (A.transpose * A).permanent) *
          ((m.factorial : ℝ) * (B.transpose * B).permanent) := by ring
    rw [hl, hr]
    exact hcs
  exact le_of_mul_le_mul_left hmul hpos
