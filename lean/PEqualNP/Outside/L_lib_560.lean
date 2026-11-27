import Mathlib

namespace PEqualNP.Outside.L_lib_560_aux

open Matrix

noncomputable def row {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => M i j)

theorem proj_ratio {n : ℕ} (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
    (x a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ V) :
    (inner ℝ x a) ^ 2 / ‖a‖ ^ 2 ≤ ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) x) ^ 2 := by
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
  rw [← hpp]
  have hxa : inner ℝ x a = inner ℝ p a := by
    have := h1 a ha
    rw [inner_sub_left] at this
    linarith
  rw [hxa]
  rcases eq_or_lt_of_le (sq_nonneg ‖a‖) with h0 | h0
  · rw [← h0, div_zero]; positivity
  · rw [div_le_iff₀ h0]
    have := abs_real_inner_le_norm p a
    have h2 : (inner ℝ p a) ^ 2 ≤ (‖p‖ * ‖a‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    nlinarith [h2]

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

theorem col_orth {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) :
    ∀ c d, (∑ i, Hᵀ c i * Hᵀ d i) = if c = d then (n : ℝ) else 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : H * ((1 / (n : ℝ)) • Hᵀ) = 1 := by
    ext i j
    have e : (H * ((1 / (n : ℝ)) • Hᵀ)) i j = (∑ c, H i c * H j c) / n := by
      simp only [Matrix.mul_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [e, hH, Matrix.one_apply]
    split_ifs <;> simp [hn']
  have h2 : ((1 / (n : ℝ)) • Hᵀ) * H = 1 := mul_eq_one_comm.1 h1
  intro c d
  have e : (((1 / (n : ℝ)) • Hᵀ) * H) c d = (∑ i, H i c * H i d) / n := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, transpose_apply, smul_eq_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h2, Matrix.one_apply, eq_div_iff hn'] at e
  simp only [transpose_apply]
  split_ifs at e ⊢ <;> linarith

theorem main {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, (∑ j, H i j * A i j) ^ 2 / (∑ j, (A i j) ^ 2)) ≤ (n : ℝ) * (A.rank : ℝ) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (LinearMap.range Aᵀ.mulVecLin).map (e : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
  have hV : Module.finrank ℝ V = A.rank := by
    rw [← rank_transpose A]
    exact LinearEquiv.finrank_map_eq e _
  let b := stdOrthonormalBasis ℝ V
  have hmem : ∀ i, row A i ∈ V := by
    intro i
    refine Submodule.mem_map.2 ⟨Aᵀ *ᵥ Pi.single i 1, ⟨Pi.single i 1, rfl⟩, ?_⟩
    rw [mulVec_single_one]
    rfl
  have hin : ∀ i, inner ℝ (row H i) (row A i) = ∑ j, H i j * A i j := by
    intro i
    simp [row, PiLp.inner_apply, mul_comm]
  have hno : ∀ i, ‖row A i‖ ^ 2 = ∑ j, (A i j) ^ 2 := by
    intro i
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [row]
  have hbi : ∀ t i, inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (row H i) = ∑ c, ((b t : EuclideanSpace ℝ (Fin n)) c) * Hᵀ c i := by
    intro t i
    simp [row, PiLp.inner_apply, mul_comm]
  have hbt : ∀ t, ∑ i, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (row H i)) ^ 2 = n := by
    intro t
    simp only [hbi]
    rw [had_sum Hᵀ (col_orth H hn hH)]
    have : ‖(b t : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      have hn1 : ‖(b t : EuclideanSpace ℝ (Fin n))‖ = 1 := b.norm_eq_one t
      rw [hn1]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at this
    rw [this, mul_one]
  have step : ∀ i, (∑ j, H i j * A i j) ^ 2 / (∑ j, (A i j) ^ 2) ≤
      ∑ t, (inner ℝ ((b t : EuclideanSpace ℝ (Fin n))) (row H i)) ^ 2 := by
    intro i
    rw [← hin, ← hno]
    exact proj_ratio V b _ _ (hmem i)
  refine le_trans (Finset.sum_le_sum (fun i _ => step i)) ?_
  rw [Finset.sum_comm]
  simp only [hbt, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hV]
  rw [mul_comm]

end PEqualNP.Outside.L_lib_560_aux

theorem PEqualNP.Outside.L_lib_560 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, (∑ j, H i j * A i j)^2 / (∑ j, (A i j)^2)) ≤ (n : ℝ) * (A.rank : ℝ) := by
  intro n H hn _ hH A
  exact PEqualNP.Outside.L_lib_560_aux.main H hn hH A
