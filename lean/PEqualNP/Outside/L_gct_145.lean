import Mathlib

theorem PEqualNP.Outside.L_gct_145 : (
  ∀ m k : ℕ, 2 * k ≤ m → (∑ w ∈ Finset.range (k + 1), m.choose w) * (k ^ k * (m - k) ^ (m - k)) ≤ m ^ m) := by
  intro m k hk
  have hkm : k ≤ m := by omega
  have hbase : k ≤ m - k := by omega
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ w ∈ Finset.range (k + 1), k ^ w * (m - k) ^ (m - w) * m.choose w := by
      apply Finset.sum_le_sum
      intro w hw
      have hwk : w ≤ k := by simpa using hw
      have hsplit : w + (k - w) = k := by omega
      have hrest : (k - w) + (m - k) = m - w := by omega
      have hterm : k ^ k * (m - k) ^ (m - k) ≤ k ^ w * (m - k) ^ (m - w) := by
        calc
          _ = k ^ w * k ^ (k - w) * (m - k) ^ (m - k) := by rw [← pow_add, hsplit]
          _ ≤ k ^ w * (m - k) ^ (k - w) * (m - k) ^ (m - k) := by gcongr
          _ = _ := by rw [mul_assoc, ← pow_add, hrest]
      simpa only [mul_comm (m.choose w)] using Nat.mul_le_mul_right (m.choose w) hterm
    _ ≤ ∑ w ∈ Finset.range (m + 1), k ^ w * (m - k) ^ (m - w) * m.choose w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intros
        exact Nat.zero_le _
    _ = (k + (m - k)) ^ m := by simpa using (add_pow k (m - k) m).symm
    _ = m ^ m := by rw [Nat.add_sub_of_le hkm]
