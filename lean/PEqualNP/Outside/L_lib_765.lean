import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_765 : (∀ (n k : ℕ), (∑ i ∈ Finset.range (k + 1), Nat.choose n i) ≤ (n + 1) ^ k) := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : n.choose (k + 1) ≤ n ^ (k + 1) := Nat.choose_le_pow n (k + 1)
    have h2 : n ^ (k + 1) ≤ n * (n + 1) ^ k := by
      rw [pow_succ']
      exact Nat.mul_le_mul_left n (Nat.pow_le_pow_left (Nat.le_succ n) k)
    calc (∑ i ∈ Finset.range (k + 1), n.choose i) + n.choose (k + 1)
        ≤ (n + 1) ^ k + n * (n + 1) ^ k := by omega
      _ = (n + 1) ^ (k + 1) := by ring
