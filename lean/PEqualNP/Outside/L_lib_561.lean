import Mathlib

namespace PEqualNP.Outside.L_lib_561_aux


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

theorem bound560 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
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

theorem row_ip {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ)
    (h1 : ∀ i j, H i j = 1 ∨ H i j = -1) (hθ : ∀ i j, |H i j - A i j| ≤ θ) (i : Fin n) :
    (n : ℝ) - θ * (∑ j, (if H i j ≠ A i j then (1 : ℝ) else 0)) ≤ ∑ j, H i j * A i j := by
  have : ∀ j, 1 - θ * (if H i j ≠ A i j then (1 : ℝ) else 0) ≤ H i j * A i j := by
    intro j
    have hb := abs_le.1 (hθ i j)
    split_ifs with h
    · rcases h1 i j with h' | h' <;> rw [h'] at hb ⊢ <;> nlinarith [hb.1, hb.2]
    · push Not at h
      rw [← h]
      rcases h1 i j with h' | h' <;> rw [h'] <;> norm_num
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => this j)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  simpa using hs

theorem row_na {n : ℕ} (H A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (h1 : ∀ i j, H i j = 1 ∨ H i j = -1) (hθ : ∀ i j, |H i j - A i j| ≤ θ) (i : Fin n) :
    ∑ j, (A i j) ^ 2 ≤ (n : ℝ) + (θ ^ 2 + 2 * θ) * (∑ j, (if H i j ≠ A i j then (1 : ℝ) else 0)) := by
  have : ∀ j, (A i j) ^ 2 ≤ 1 + (θ ^ 2 + 2 * θ) * (if H i j ≠ A i j then (1 : ℝ) else 0) := by
    intro j
    have hb := abs_le.1 (hθ i j)
    split_ifs with h
    · rcases h1 i j with h' | h' <;> rw [h'] at hb <;> nlinarith [hb.1, hb.2]
    · push Not at h
      rw [← h]
      rcases h1 i j with h' | h' <;> rw [h'] <;> norm_num
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => this j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simpa using hs

theorem term_ge (ip na dd n θ c : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hdd : 0 ≤ dd)
    (hip : n - θ * dd ≤ ip) (hna : na ≤ n + c * dd) (hna0 : 0 ≤ na) (hz : na = 0 → ip = 0) :
    (max 0 (n - θ * dd)) ^ 2 / (n + c * dd) ≤ ip ^ 2 / na := by
  have hy : 0 < n + c * dd := by positivity
  rcases eq_or_lt_of_le hna0 with h0 | h0
  · have := hz h0.symm
    rw [this] at hip
    have : max 0 (n - θ * dd) = 0 := max_eq_left (by linarith)
    rw [this]
    have e : (0 : ℝ) ^ 2 / (n + c * dd) = 0 := by simp
    rw [e]
    positivity
  · rcases le_total (n - θ * dd) 0 with hu | hu
    · rw [max_eq_left hu]; simp; positivity
    · rw [max_eq_right hu]
      have hsq : (n - θ * dd) ^ 2 ≤ ip ^ 2 := pow_le_pow_left₀ hu hip 2
      calc (n - θ * dd) ^ 2 / (n + c * dd) ≤ ip ^ 2 / (n + c * dd) :=
            div_le_div_of_nonneg_right hsq hy.le
        _ ≤ ip ^ 2 / na := div_le_div_of_nonneg_left (sq_nonneg _) h0 hna

theorem main {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (h1 : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hH : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : ∀ i j, |H i j - A i j| ≤ θ) :
    (n : ℝ) ^ 2 * ((n : ℝ) - (A.rank : ℝ)) ≤
      (((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => H p.1 p.2 ≠ A p.1 p.2)).card : ℝ) *
        (2 * θ * n + (A.rank : ℝ) * (θ ^ 2 + 2 * θ)) := by
  set c := θ ^ 2 + 2 * θ with hcdef
  have hc : 0 ≤ c := by positivity
  set r : ℝ := (A.rank : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hnr : (n : ℝ) > 0 := by exact_mod_cast hn
  let d : Fin n → ℝ := fun i => ∑ j, (if H i j ≠ A i j then (1 : ℝ) else 0)
  have hd0 : ∀ i, 0 ≤ d i := fun i => Finset.sum_nonneg (fun j _ => by split_ifs <;> norm_num)
  have hD : (((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => H p.1 p.2 ≠ A p.1 p.2)).card : ℝ)
      = ∑ i, d i := by
    rw [Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
  rw [hD]
  set D := ∑ i, d i with hDdef
  have hb := bound560 H hn hH A
  let u : Fin n → ℝ := fun i => max 0 ((n : ℝ) - θ * d i)
  have hterm : ∀ i, (u i) ^ 2 / ((n : ℝ) + c * d i) ≤
      (∑ j, H i j * A i j) ^ 2 / (∑ j, (A i j) ^ 2) := by
    intro i
    apply term_ge _ _ _ _ _ _ hnr hc (hd0 i) (row_ip H A θ h1 hθ i) (row_na H A θ hθ0 h1 hθ i)
      (Finset.sum_nonneg (fun j _ => sq_nonneg _))
    intro h0
    have : ∀ j, A i j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
        sq_nonneg (A i j))).1 h0 j (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [this]
  have htitu := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin n)) u
    (g := fun i => (n : ℝ) + c * d i) (fun i _ => by have := hd0 i; positivity)
  have hsumg : ∑ i, ((n : ℝ) + c * d i) = (n : ℝ) ^ 2 + c * D := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp; ring
  have hsumu : (n : ℝ) ^ 2 - θ * D ≤ ∑ i, u i := by
    have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (n : ℝ) - θ * d i ≤ u i := fun i _ => le_max_right _ _
    have hs := Finset.sum_le_sum this
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
    simp at hs
    nlinarith [hs]
  have hchain : (∑ i, u i) ^ 2 / ((n : ℝ) ^ 2 + c * D) ≤ n * r := by
    rw [← hsumg]
    exact le_trans htitu (le_trans (Finset.sum_le_sum (fun i _ => hterm i)) hb)
  have hD0 : 0 ≤ D := Finset.sum_nonneg (fun i _ => hd0 i)
  have hg0 : 0 < (n : ℝ) ^ 2 + c * D := by positivity
  rw [div_le_iff₀ hg0] at hchain
  have hrn : r ≤ n := by
    rw [hr]
    have := Matrix.rank_le_card_width A
    simp at this
    exact_mod_cast this
  rcases le_total ((n : ℝ) ^ 2 - θ * D) 0 with hneg | hpos
  · nlinarith [mul_nonneg hD0 (mul_nonneg hr0 hc), mul_nonneg hnr.le (mul_nonneg hnr.le hr0)]
  · have hsq : ((n : ℝ) ^ 2 - θ * D) ^ 2 ≤ (∑ i, u i) ^ 2 := pow_le_pow_left₀ hpos hsumu 2
    have key : (n : ℝ) * ((n : ℝ) ^ 2 * ((n : ℝ) - r)) ≤ (n : ℝ) * (D * (2 * θ * n + r * c)) := by
      nlinarith [sq_nonneg (θ * D)]
    exact le_of_mul_le_mul_left key hnr

end PEqualNP.Outside.L_lib_561_aux

theorem PEqualNP.Outside.L_lib_561 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ (A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ), 0 ≤ θ →
    (∀ i j, |H i j - A i j| ≤ θ) →
    let D := ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => H p.1 p.2 ≠ A p.1 p.2)).card
    (n : ℝ)^2 * ((n : ℝ) - (A.rank : ℝ)) ≤
      (D : ℝ) * (2*θ*n + (A.rank : ℝ)*(θ^2+2*θ)) := by
  intro n H hn h1 hH A θ hθ0 hθ D
  exact PEqualNP.Outside.L_lib_561_aux.main H hn h1 hH A θ hθ0 hθ
