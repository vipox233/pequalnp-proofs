import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_776

theorem term_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) : a - b ≤ a * Real.log (a / b) := by
  rcases ha.eq_or_lt with h | hpos
  · subst h
    simp
    exact hb.le
  · have h := Real.log_le_sub_one_of_pos (div_pos hb hpos)
    rw [Real.log_div hb.ne' hpos.ne'] at h
    rw [Real.log_div hpos.ne' hb.ne']
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    have e : a * (b / a - 1) = b - a := by
      field_simp
    rw [e] at h2
    linarith

end PEqualNP.Outside.L_lib_776

theorem PEqualNP.Outside.L_lib_776 : ∀ (k : ℕ) (p q : Fin k → ℝ), (∀ i, 0 ≤ p i) → (∀ i, 0 < q i) →
  (∑ i, p i) = 1 → (∑ i, q i) ≤ 1 →
  0 ≤ ∑ i, p i * Real.log (p i / q i) := by
  intro k p q hp hq hp1 hq1
  have h : ∑ i, (p i - q i) ≤ ∑ i, p i * Real.log (p i / q i) :=
    Finset.sum_le_sum fun i _ => PEqualNP.Outside.L_lib_776.term_le (p i) (q i) (hp i) (hq i)
  rw [Finset.sum_sub_distrib] at h
  linarith
