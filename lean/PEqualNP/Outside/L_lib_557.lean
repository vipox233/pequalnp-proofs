import Mathlib

namespace PEqualNP.Outside.L_lib_557_aux

open Matrix

noncomputable def col {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => M i j)

theorem proj_bound {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    (x a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ V) :
    ‖x‖ ^ 2 - ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x) ^ 2 ≤ ‖x - a‖ ^ 2 := by
  set p := V.starProjection x with hp
  have hpV : p ∈ V := V.starProjection_apply_mem x
  have h1 : ∀ w ∈ V, inner ℝ (x - p) w = 0 := fun w hw => V.starProjection_inner_eq_zero x w hw
  have hpp : ‖p‖ ^ 2 = ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x) ^ 2 := by
    have := b.sum_sq_norm_inner_right ⟨p, hpV⟩
    have e : ‖(⟨p, hpV⟩ : V)‖ = ‖p‖ := rfl
    rw [e] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro t _
    have e2 : inner ℝ (b t) (⟨p, hpV⟩ : V) = inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) p := rfl
    rw [e2, Real.norm_eq_abs, sq_abs]
    have e3 := h1 _ (b t).2
    rw [real_inner_comm, inner_sub_right] at e3
    rw [show inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) p = inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x by linarith]
  have hxa : x - a = (x - p) + (p - a) := by abel
  have hx : x = (x - p) + p := by abel
  have i1 : inner ℝ (x - p) (p - a) = 0 := h1 _ (V.sub_mem hpV ha)
  have i2 : inner ℝ (x - p) p = 0 := h1 _ hpV
  have n1 : ‖x - a‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - a‖ ^ 2 := by
    rw [hxa, norm_add_sq_real, i1]; ring
  have n2 : ‖x‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p‖ ^ 2 := by
    conv_lhs => rw [hx]
    rw [norm_add_sq_real, i2]; ring
  rw [← hpp]
  nlinarith [sq_nonneg ‖p - a‖]

theorem had_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (v : Fin n → ℝ) :
    ∑ j, (∑ i, v i * H i j) ^ 2 = n * ∑ i, v i ^ 2 := by
  calc ∑ j, (∑ i, v i * H i j) ^ 2 = ∑ j, ∑ i, ∑ k, (v i * v k) * (H i j * H k j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sq, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = ∑ i, ∑ k, (v i * v k) * ∑ j, H i j * H k j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
    _ = n * ∑ i, v i ^ 2 := by
        simp only [hH, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

theorem inner_col {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) (M : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    inner ℝ u (col M j) = ∑ i, u i * M i j := by
  simp [col, PiLp.inner_apply, mul_comm]

theorem norm_col_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    ‖col M j - col N j‖ ^ 2 = ∑ i, (M i j - N i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [col]

theorem lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h1 : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.rank ≤ r) :
    (n : ℝ) * n - n * r ≤ ∑ i, ∑ j, (H i j - A i j) ^ 2 := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (LinearMap.range A.mulVecLin).map (e : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hV : Module.finrank ℝ V = A.rank := LinearEquiv.finrank_map_eq e _
  let b := stdOrthonormalBasis ℝ V
  have hmem : ∀ j, col A j ∈ V := by
    intro j
    refine Submodule.mem_map.2 ⟨A *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩, ?_⟩
    rw [mulVec_single_one]
    rfl
  have hsq : ∀ i j, H i j ^ 2 = 1 := by
    intro i j
    rcases h1 i j with h | h <;> rw [h] <;> norm_num
  have hHn : ∀ j, ‖col H j‖ ^ 2 = n := by
    intro j
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [col, hsq]
  have hbt : ∀ t, ∑ j, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (col H j)) ^ 2 = n := by
    intro t
    simp only [inner_col]
    rw [had_sum H hH]
    have : ‖(b t : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      have hn1 : ‖(b t : EuclideanSpace ℝ (Fin n))‖ = 1 := b.norm_eq_one t
      rw [hn1]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at this
    rw [this, mul_one]
  have step : ∀ j, ‖col H j‖ ^ 2 - ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (col H j)) ^ 2
      ≤ ∑ i, (H i j - A i j) ^ 2 := by
    intro j
    rw [← norm_col_sub]
    exact proj_bound V b _ _ (hmem j)
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => step j)
  rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun j t => _)] at hsum
  simp only [hHn, hbt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [Finset.sum_comm] at hsum
  have hr : (Module.finrank ℝ V : ℝ) ≤ r := by rw [hV]; exact_mod_cast hA
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_left hr hn0]

theorem upper {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (h1 : ∀ i j, H i j = 1 ∨ H i j = -1)
    (r : ℕ) (hr : r ≤ n) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A.rank ≤ r ∧
      ∑ i, ∑ j, (H i j - A i j) ^ 2 = (n : ℝ) * ((n - r : ℕ) : ℝ) := by
  classical
  let d : Fin n → ℝ := fun i => if i.val < r then 1 else 0
  refine ⟨diagonal d * H, ?_, ?_⟩
  · refine le_trans (rank_mul_le_left _ _) ?_
    rw [rank_diagonal]
    apply le_of_eq
    have : Fintype.card {i : Fin n // d i ≠ 0} = Fintype.card (Fin r) := by
      apply Fintype.card_congr
      exact {
        toFun := fun i => ⟨i.1.val, by
          have := i.2
          simp only [d, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at this
          exact this⟩
        invFun := fun k => ⟨⟨k.val, by omega⟩, by simp [d]⟩
        left_inv := fun i => by ext; simp
        right_inv := fun k => by ext; simp }
    rw [this, Fintype.card_fin]
  · have hsq : ∀ i j, H i j ^ 2 = 1 := by
      intro i j
      rcases h1 i j with h | h <;> rw [h] <;> norm_num
    have row : ∀ i : Fin n, ∑ j, (H i j - (diagonal d * H) i j) ^ 2 =
        if i.val < r then 0 else (n : ℝ) := by
      intro i
      simp only [diagonal_mul, d]
      split_ifs <;> simp [hsq]
    simp only [row]
    rw [Fin.sum_univ_eq_sum_range (fun k => if k < r then (0 : ℝ) else (n : ℝ)) n]
    obtain ⟨m, rfl⟩ : ∃ m, n = r + m := ⟨n - r, by omega⟩
    rw [Finset.sum_range_add]
    rw [Finset.sum_eq_zero (fun k hk => by simp [Finset.mem_range.1 hk])]
    simp
    ring

end PEqualNP.Outside.L_lib_557_aux

theorem PEqualNP.Outside.L_lib_557 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ r : ℕ, r ≤ n →
    let err := fun (A : Matrix (Fin n) (Fin n) ℝ) => ∑ i, ∑ j, (H i j - A i j)^2
    let best : ℝ := n * (n-r : ℕ)
    (∀ A, A.rank ≤ r → best ≤ err A) ∧ (∃ A, A.rank ≤ r ∧ err A = best) := by
  intro n H hn h1 hH r hr err best
  refine ⟨fun A hA => ?_, ?_⟩
  · have := PEqualNP.Outside.L_lib_557_aux.lower H h1 hH r A hA
    show (n : ℝ) * ((n - r : ℕ) : ℝ) ≤ ∑ i, ∑ j, (H i j - A i j) ^ 2
    rw [Nat.cast_sub hr]
    linarith
  · exact PEqualNP.Outside.L_lib_557_aux.upper H h1 r hr
