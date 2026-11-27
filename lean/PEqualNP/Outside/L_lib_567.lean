import PEqualNP.Defs

-- L-lib-567 (same proof as our L-lib-564, block sizes now depend on j):
-- test the Parseval identity on x = v i a. Its own block contributes exactly w i (orthonormal
-- block), every other block contributes a nonnegative amount, and the total is dot x x = 1. So w i is at
-- most 1, and when w i = 1 every other term vanishes, which with w j positive kills each overlap.

theorem PEqualNP.Outside.L_lib_567 :
    ∀ (n k : ℕ) (m : Fin k → ℕ) (v : (j : Fin k) → Fin (m j) → Fin n → ℝ) (w : Fin k → ℝ),
      (∀ j, 0 < m j) →
      let dot := fun (x y : Fin n → ℝ) => ∑ i, x i * y i
      (∀ j, 0 ≤ w j) →
      (∀ j a b, dot (v j a) (v j b) = if a = b then 1 else 0) →
      (∀ x, (∑ j, w j * (∑ a, (dot x (v j a))^2)) = dot x x) →
      (∀ j, w j ≤ 1) ∧
        ∀ i j, i ≠ j → w i = 1 → 0 < w j → ∀ a b, dot (v i a) (v j b) = 0
      := by
  intro n k m v w hm dot hw horth hpar
  have nonneg : ∀ (x : Fin n → ℝ) (j : Fin k), 0 ≤ w j * ∑ b, (dot x (v j b))^2 :=
    fun x j => mul_nonneg (hw j) (Finset.sum_nonneg fun b _ => sq_nonneg _)
  have key : ∀ i a, w i + ∑ j ∈ Finset.univ.erase i, w j * ∑ b, (dot (v i a) (v j b))^2 = 1 := by
    intro i a
    have h1 := hpar (v i a)
    rw [horth i a a, if_pos rfl, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h1
    have h2 : ∑ b, (dot (v i a) (v i b))^2 = 1 := by
      simp only [horth i a]
      simp [ite_pow]
    rw [h2, mul_one] at h1
    exact h1
  constructor
  · intro j
    have h := key j ⟨0, hm j⟩
    have hR := Finset.sum_nonneg (s := Finset.univ.erase j) fun j' _ => nonneg (v j ⟨0, hm j⟩) j'
    linarith
  · intro i j hij hi1 hj a b
    have h := key i a
    rw [hi1] at h
    have hR : ∑ j ∈ Finset.univ.erase i, w j * ∑ b, (dot (v i a) (v j b))^2 = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => nonneg (v i a) j')] at hR
    have h3 := hR j (Finset.mem_erase.2 ⟨fun e => hij e.symm, Finset.mem_univ _⟩)
    rcases mul_eq_zero.1 h3 with h0 | h0
    · linarith
    · rw [Finset.sum_eq_zero_iff_of_nonneg (fun b' _ => sq_nonneg _)] at h0
      exact (pow_eq_zero_iff two_ne_zero).1 (h0 b (Finset.mem_univ b))
