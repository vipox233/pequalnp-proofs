import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_430

lemma rank_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hmul : (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by
    ext x i
    simp
  have hle : LinearMap.range (A + B).mulVecLin ≤
      (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule ℚ (Fin n → ℚ)) := by
    rintro y ⟨x, rfl⟩
    rw [hmul, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ x)
  calc
    (A + B).rank = Module.finrank ℚ (LinearMap.range (A + B).mulVecLin) := rfl
    _ ≤ Module.finrank ℚ
          (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule ℚ (Fin n → ℚ)) :=
      Submodule.finrank_mono hle
    _ ≤ Module.finrank ℚ (LinearMap.range A.mulVecLin) +
          Module.finrank ℚ (LinearMap.range B.mulVecLin) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    _ = A.rank + B.rank := rfl

lemma rank_sum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Matrix (Fin n) (Fin n) ℚ) :
    (∑ p ∈ s, F p).rank ≤ ∑ p ∈ s, (F p).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le _ _).trans (Nat.add_le_add_left ih _)

lemma dhs_bound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ)
    (hdiag : ∀ i, M i i ≠ 0) (hoff : ∀ i j, i ≠ j → M i j * M j i = 0) :
    n ≤ M.rank ^ 2 := by
  classical
  let r : ℕ := M.rank
  let b : Module.Basis (Fin r) ℚ (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq ℚ (LinearMap.range M.mulVecLin) rfl
  let u : Fin r → Fin n → ℚ := fun k i => (b k).1 i
  let v : Fin r → Fin n → ℚ := fun k j =>
    b.repr ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩ k
  have hM_eq : ∀ i j : Fin n, M i j = ∑ k : Fin r, u k i * v k j := by
    intro i j
    have hsum := congrArg Subtype.val
      (b.sum_repr ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩)
    rw [Submodule.coe_sum] at hsum
    have hval := congr_fun hsum i
    have hcol : (M.mulVecLin (Pi.single j 1)) i = M i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, hcol] at hval
    rw [← hval]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact mul_comm (v k j) (u k i)
  let D : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => M i j * M j i
  have hD_diag : D = Matrix.diagonal (fun i => M i i * M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [D]
    · simp [D, hij, hoff i j hij]
  have hD_rank_eq : D.rank = n := by
    rw [hD_diag, Matrix.rank_diagonal]
    have hcard : Fintype.card {i : Fin n // M i i * M i i ≠ 0} = Fintype.card (Fin n) :=
      Fintype.card_congr
        ⟨fun x => x.1, fun i => ⟨i, mul_ne_zero (hdiag i) (hdiag i)⟩, fun _ => rfl, fun _ => rfl⟩
    rw [hcard, Fintype.card_fin]
  let P : Fin r × Fin r → Matrix (Fin n) (Fin n) ℚ :=
    fun p => Matrix.vecMulVec (fun i => u p.1 i * v p.2 i) (fun j => v p.1 j * u p.2 j)
  have hD_sum : D = ∑ p : Fin r × Fin r, P p := by
    ext i j
    simp only [D, Matrix.of_apply, P, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Fintype.sum_prod_type]
    rw [hM_eq i j, hM_eq j i, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hD_rank_le : D.rank ≤ r ^ 2 := by
    rw [hD_sum]
    calc
      (∑ p : Fin r × Fin r, P p).rank ≤ ∑ p : Fin r × Fin r, (P p).rank :=
        rank_sum_le Finset.univ P
      _ ≤ ∑ _p : Fin r × Fin r, 1 := by
        refine Finset.sum_le_sum fun p _ => ?_
        exact Matrix.rank_vecMulVec_le _ _
      _ = Fintype.card (Fin r × Fin r) := by simp
      _ = r ^ 2 := by simp [pow_two]
  dsimp [r] at hD_rank_le
  exact hD_rank_eq.symm.le.trans hD_rank_le

end PEqualNP.Outside.L_lib_430

theorem PEqualNP.Outside.L_lib_430 : (∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
  (∀ i, M i i ≠ 0) → (∀ i j, i ≠ j → M i j * M j i = 0) →
  n ≤ M.rank ^ 2) := by
  exact PEqualNP.Outside.L_lib_430.dhs_bound
