import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_764_aux

theorem sgn {k : ℕ} (p : Fin k → Prop) [DecidablePred p] :
    (if (Finset.univ.filter p).card % 2 = 0 then (1 : ℤ) else -1) =
      ∏ i, (if p i then (-1 : ℤ) else 1) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_univ, one_pow, mul_one]
  rcases Nat.even_or_odd (Finset.univ.filter p).card with h | h
  · rw [h.neg_one_pow, if_pos (Nat.even_iff.mp h)]
  · rw [h.neg_one_pow, if_neg (by have := Nat.odd_iff.mp h; omega)]

end PEqualNP.Outside.L_lib_764_aux

open PEqualNP.Outside.L_lib_764_aux in
theorem PEqualNP.Outside.L_lib_764 : ∀ (k : ℕ) (x y : Fin k → Bool), x ≠ y →
  (∑ z : Fin k → Bool,
    (if (Finset.univ.filter (fun i => x i = true ∧ z i = true)).card % 2 = 0 then (1 : ℤ) else -1) *
    (if (Finset.univ.filter (fun i => y i = true ∧ z i = true)).card % 2 = 0 then (1 : ℤ) else -1)) = 0 := by
  intro k x y hxy
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hxy
  simp_rw [sgn, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => (if x i = true ∧ b = true then (-1 : ℤ) else 1) *
    (if y i = true ∧ b = true then (-1 : ℤ) else 1))]
  apply Finset.prod_eq_zero (Finset.mem_univ i0)
  cases hx : x i0 <;> cases hy : y i0 <;> simp_all
