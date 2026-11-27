import Mathlib

namespace PEqualNP.Outside.L_lib_563_aux

theorem main (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hpm : ∀ i j, H i j = 1 ∨ H i j = -1)
    (horth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    n ≤ (Finset.univ.filter (fun i => x i ≠ 0)).card *
      (Finset.univ.filter (fun i => H.mulVec x i ≠ 0)).card := by
  set y := H.mulVec x with hy
  set A := Finset.univ.filter (fun i => x i ≠ 0)
  set B := Finset.univ.filter (fun i => y i ≠ 0)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hHH : H * H.transpose = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, horth, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hTH : H.transpose * H = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have h1 : H * ((n : ℝ)⁻¹ • H.transpose) = 1 := by
      rw [Matrix.mul_smul, hHH, smul_smul, inv_mul_cancel₀ hnr.ne', one_smul]
    have h2 := (mul_eq_one_comm.mp h1)
    rw [Matrix.smul_mul] at h2
    have h3 := congrArg (fun M => (n : ℝ) • M) h2
    simp only [smul_smul, mul_inv_cancel₀ hnr.ne', one_smul] at h3
    exact h3
  have hpar : ∑ i, y i ^ 2 = (n : ℝ) * ∑ c, x c ^ 2 := by
    have e1 : ∑ i, y i ^ 2 = y ⬝ᵥ y := by simp [dotProduct, sq]
    have e2 : ∑ c, x c ^ 2 = x ⬝ᵥ x := by simp [dotProduct, sq]
    rw [e1, e2, hy, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
    rw [hTH]
    simp [Matrix.smul_mulVec, smul_dotProduct]
  have hyb : ∀ i, |y i| ≤ ∑ c ∈ A, |x c| := by
    intro i
    have : y i = ∑ c, H i c * x c := rfl
    rw [this]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c => x c ≠ 0)]
    have h0 : ∑ c ∈ Finset.univ.filter (fun c => ¬ x c ≠ 0), |H i c * x c| = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      simp only [Finset.mem_filter, not_not] at hc
      simp [hc.2]
    rw [h0, add_zero]
    apply Finset.sum_le_sum
    intro c _
    rw [abs_mul]
    rcases hpm i c with h | h <;> simp [h]
  have hy2 : ∑ i, y i ^ 2 ≤ B.card * (∑ c ∈ A, |x c|) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => y i ≠ 0)]
    have h0 : ∑ i ∈ Finset.univ.filter (fun i => ¬ y i ≠ 0), y i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      simp only [Finset.mem_filter, not_not] at hc
      simp [hc.2]
    rw [h0, add_zero]
    have : ∑ i ∈ B, y i ^ 2 ≤ ∑ i ∈ B, (∑ c ∈ A, |x c|) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hyb i) 2
    simpa using this
  have hx1 : (∑ c ∈ A, |x c|) ^ 2 ≤ A.card * ∑ c, x c ^ 2 := by
    refine le_trans (sq_sum_le_card_mul_sum_sq) ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    simp only [sq_abs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _)
  have hQ : 0 < ∑ c, x c ^ 2 := by
    obtain ⟨c, hc⟩ : ∃ c, x c ≠ 0 := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun c => x c ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ c))
  have key : (n : ℝ) * ∑ c, x c ^ 2 ≤ ((A.card * B.card : ℕ) : ℝ) * ∑ c, x c ^ 2 := by
    rw [← hpar]
    refine le_trans hy2 ?_
    push_cast
    calc (B.card : ℝ) * (∑ c ∈ A, |x c|) ^ 2 ≤ B.card * (A.card * ∑ c, x c ^ 2) :=
          mul_le_mul_of_nonneg_left hx1 (Nat.cast_nonneg _)
      _ = A.card * B.card * ∑ c, x c ^ 2 := by ring
  have := le_of_mul_le_mul_right key hQ
  exact_mod_cast this

end PEqualNP.Outside.L_lib_563_aux

theorem PEqualNP.Outside.L_lib_563 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ x : Fin n → ℝ, x ≠ 0 →
    let y := H.mulVec x
    n ≤ (Finset.univ.filter (fun i => x i ≠ 0)).card *
      (Finset.univ.filter (fun i => y i ≠ 0)).card := by
  intro n H hn hpm horth x hx y
  exact PEqualNP.Outside.L_lib_563_aux.main n H hn hpm horth x hx
