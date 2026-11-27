import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_558 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ (a b : ℕ) (rows : Fin a ↪ Fin n) (cols : Fin b ↪ Fin n),
    a * b ≤ n * (H.submatrix rows cols).rank) := by
  intro n H _ hpm horth a b rows cols
  let S : Matrix (Fin a) (Fin b) ℝ := H.submatrix rows cols
  let e : (Fin a → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a) := (EuclideanSpace.equiv (Fin a) ℝ).symm
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin a)) :=
    Submodule.map e.toLinearMap (LinearMap.range S.mulVecLin)
  have hrank : Module.finrank ℝ U = S.rank := by
    rw [Matrix.rank]
    exact e.finrank_map_eq (LinearMap.range S.mulVecLin)
  let r := Module.finrank ℝ U
  let B : OrthonormalBasis (Fin r) ℝ U := stdOrthonormalBasis ℝ U
  have hcol_mem : ∀ j : Fin b, e (fun i => S i j) ∈ U := by
    intro j
    refine Submodule.mem_map.mpr ⟨fun i => S i j, ?_, rfl⟩
    refine ⟨Pi.single j (1 : ℝ), ?_⟩
    funext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hcol_parseval : ∀ j : Fin b,
      (∑ k : Fin r, (∑ i : Fin a, (B k : EuclideanSpace ℝ (Fin a)) i * S i j) ^ 2) = (a : ℝ) := by
    intro j
    let u : U := ⟨e (fun i => S i j), hcol_mem j⟩
    have hpar := B.sum_sq_inner_right u
    have hnorm_sq : ‖u‖ ^ 2 = (a : ℝ) := by
      have h1 : ‖u‖ ^ 2 = ‖e (fun i => S i j)‖ ^ 2 := rfl
      rw [h1, EuclideanSpace.norm_sq_eq]
      have hterm : ∀ i : Fin a, ‖(e (fun i => S i j)) i‖ ^ 2 = (1 : ℝ) := by
        intro i
        rw [Real.norm_eq_abs, sq_abs]
        have hSpm : S i j = 1 ∨ S i j = -1 := hpm (rows i) (cols j)
        change (S i j) ^ 2 = 1
        rcases hSpm with h | h <;> rw [h] <;> norm_num
      have hsum : (∑ i : Fin a, ‖(e (fun i => S i j)) i‖ ^ 2) = (a : ℝ) := by
        rw [Finset.sum_congr rfl (fun i _ => hterm i)]
        simp
      exact hsum
    rw [hnorm_sq] at hpar
    rw [← hpar]
    refine Finset.sum_congr rfl ?_
    intro k _
    congr 1
    change ∑ i : Fin a, (B k : EuclideanSpace ℝ (Fin a)) i * S i j =
      @inner ℝ U _ (B k) u
    rw [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct]
    unfold dotProduct
    refine Finset.sum_congr rfl ?_
    intro i _
    change (B k : EuclideanSpace ℝ (Fin a)) i * S i j =
      S i j * star ((B k : EuclideanSpace ℝ (Fin a)) i)
    rw [star_trivial, mul_comm]
  have hrow_bound : ∀ k : Fin r,
      (∑ j : Fin b, (∑ i : Fin a, (B k : EuclideanSpace ℝ (Fin a)) i * S i j) ^ 2) ≤ (n : ℝ) := by
    intro k
    let v : Fin a → ℝ := fun i => (B k : EuclideanSpace ℝ (Fin a)) i
    have hv_norm : (∑ i : Fin a, (v i) ^ 2) = 1 := by
      have h1 : ‖(B k : EuclideanSpace ℝ (Fin a))‖ ^ 2 = 1 := by
        have hunit := B.orthonormal.1 k
        have : ‖(B k : EuclideanSpace ℝ (Fin a))‖ = 1 := hunit
        rw [this, one_pow]
      rw [EuclideanSpace.norm_sq_eq] at h1
      convert h1 using 1
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Real.norm_eq_abs, sq_abs]
    have hle_all :
        (∑ j : Fin b, (∑ i : Fin a, v i * H (rows i) (cols j)) ^ 2) ≤
          ∑ c : Fin n, (∑ i : Fin a, v i * H (rows i) c) ^ 2 := by
      have himg :
          (∑ j : Fin b, (∑ i : Fin a, v i * H (rows i) (cols j)) ^ 2) =
            ∑ c ∈ Finset.univ.image cols, (∑ i : Fin a, v i * H (rows i) c) ^ 2 := by
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact cols.injective hxy
      rw [himg]
      exact Finset.sum_le_univ_sum_of_nonneg (fun c => sq_nonneg _)
    have hexpand :
        (∑ c : Fin n, (∑ i : Fin a, v i * H (rows i) c) ^ 2) = (n : ℝ) := by
      have hsq : ∀ c : Fin n,
          (∑ i : Fin a, v i * H (rows i) c) ^ 2 =
            ∑ i1 : Fin a, ∑ i2 : Fin a, (v i1 * v i2) * (H (rows i1) c * H (rows i2) c) := by
        intro c
        rw [sq, Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro i1 _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i2 _
        ring
      simp_rw [hsq]
      rw [Finset.sum_comm]
      have hswap2 :
          (∑ i1 : Fin a, ∑ c : Fin n, ∑ i2 : Fin a,
            (v i1 * v i2) * (H (rows i1) c * H (rows i2) c)) =
          ∑ i1 : Fin a, ∑ i2 : Fin a,
            (v i1 * v i2) * (∑ c : Fin n, H (rows i1) c * H (rows i2) c) := by
        refine Finset.sum_congr rfl ?_
        intro i1 _
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro i2 _
        rw [Finset.mul_sum]
      rw [hswap2]
      have hdiag : ∀ i1 : Fin a,
          (∑ i2 : Fin a, (v i1 * v i2) * (∑ c : Fin n, H (rows i1) c * H (rows i2) c)) =
            (v i1) ^ 2 * (n : ℝ) := by
        intro i1
        simp_rw [horth]
        rw [Finset.sum_eq_single i1]
        · simp [sq]
        · intro i2 _ hne
          have hrne : rows i1 ≠ rows i2 := fun h => hne (rows.injective h).symm
          simp [hrne]
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ i1))
      simp_rw [hdiag, ← Finset.sum_mul, hv_norm, one_mul]
    exact le_trans hle_all (le_of_eq hexpand)
  have hreal : ((a * b : ℕ) : ℝ) ≤ ((n * S.rank : ℕ) : ℝ) := by
    have hsum1 :
        (∑ j : Fin b, ∑ k : Fin r,
          (∑ i : Fin a, (B k : EuclideanSpace ℝ (Fin a)) i * S i j) ^ 2) = (a : ℝ) * (b : ℝ) := by
      simp_rw [hcol_parseval]
      simp [mul_comm]
    have hsum2 :
        (∑ k : Fin r, ∑ j : Fin b,
          (∑ i : Fin a, (B k : EuclideanSpace ℝ (Fin a)) i * S i j) ^ 2) ≤ (r : ℝ) * (n : ℝ) := by
      calc
        (∑ k : Fin r, ∑ j : Fin b,
            (∑ i : Fin a, (B k : EuclideanSpace ℝ (Fin a)) i * S i j) ^ 2)
            ≤ ∑ _k : Fin r, (n : ℝ) := Finset.sum_le_sum (fun k _ => hrow_bound k)
        _ = (r : ℝ) * (n : ℝ) := by simp
    rw [Finset.sum_comm] at hsum1
    rw [hsum1] at hsum2
    have hr_eq : (r : ℝ) = (S.rank : ℝ) := by exact_mod_cast hrank
    rw [hr_eq] at hsum2
    push_cast
    linarith
  exact_mod_cast hreal
