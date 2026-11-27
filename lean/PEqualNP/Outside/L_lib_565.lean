import Mathlib

namespace PEqualNP.Outside.L_lib_565_aux

theorem swap_eq (n k : ℕ) (v : Fin k → Fin n → ℝ) :
    ∑ a, ∑ b, (∑ i, v a i * v b i) ^ 2 = ∑ i, ∑ j, (∑ a, v a i * v a j) ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem main (n k : ℕ) (v : Fin k → Fin n → ℝ) (h : ∀ j, ∑ i, v j i * v j i = 1) :
    (k : ℝ) ^ 2 ≤ (n : ℝ) * ∑ a, ∑ b, (∑ i, v a i * v b i) ^ 2 := by
  rw [swap_eq]
  have htr : ∑ i, (∑ a, v a i * v a i) = (k : ℝ) := by
    rw [Finset.sum_comm]
    simp [h]
  have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => ∑ a, v a i * v a i)
  rw [htr] at h1
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  refine le_trans h1 ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (f := fun j => (∑ a, v a i * v a j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

end PEqualNP.Outside.L_lib_565_aux

theorem PEqualNP.Outside.L_lib_565 : ∀ (n k : ℕ) (v : Fin k → Fin n → ℝ),
  let dot := fun (x y : Fin n → ℝ) => ∑ i, x i * y i
  (∀ j, dot (v j) (v j) = 1) →
    (k : ℝ)^2 ≤ (n : ℝ) * ∑ a, ∑ b, (dot (v a) (v b))^2 := by
  intro n k v dot h
  exact PEqualNP.Outside.L_lib_565_aux.main n k v h
