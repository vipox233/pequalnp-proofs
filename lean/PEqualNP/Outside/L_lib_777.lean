import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_777_aux

theorem exists_ge_average (n : ℕ) (w f : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1) :
    ∃ i, (∑ j, w j * f j) ≤ f i := by
  classical
  have hpos : ∃ i, 0 < w i := by
    by_contra hn
    have hz : (∑ i, w i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact le_antisymm (le_of_not_gt (fun hi => hn ⟨i, hi⟩)) (hw i)
    linarith
  obtain ⟨i, hi⟩ := hpos
  by_contra hn
  have hf : ∀ j, f j < ∑ k, w k * f k := by
    intro j
    exact lt_of_not_ge (fun hj => hn ⟨j, hj⟩)
  have hlt : (∑ j, w j * f j) < ∑ j, w j * (∑ k, w k * f k) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_le_mul_of_nonneg_left (hf j).le (hw j)
    · exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (hf i) hi⟩
  rw [← Finset.sum_mul, hs, one_mul] at hlt
  exact lt_irrefl _ hlt

end PEqualNP.Outside.L_lib_777_aux

theorem PEqualNP.Outside.L_lib_777 : (∀ (a b : ℕ) (M : Fin a → Fin b → ℝ) (p : Fin a → ℝ) (q : Fin b → ℝ),
  (∀ i, 0 ≤ p i) → (∀ j, 0 ≤ q j) → (∑ i, p i) = 1 → (∑ j, q j) = 1 →
  ∃ (j : Fin b) (i : Fin a), (∑ i', p i' * M i' j) ≤ ∑ j', q j' * M i j') := by
  classical
  intro a b M p q hp hq hps hqs
  let col : Fin b → ℝ := fun j => ∑ i, p i * M i j
  let row : Fin a → ℝ := fun i => ∑ j, q j * M i j
  obtain ⟨i, hi⟩ := PEqualNP.Outside.L_lib_777_aux.exists_ge_average a p row hp hps
  obtain ⟨j, hj⟩ := PEqualNP.Outside.L_lib_777_aux.exists_ge_average b q (fun j => -col j) hq hqs
  simp only [mul_neg, Finset.sum_neg_distrib, neg_le_neg_iff] at hj
  have hswap : (∑ j, q j * col j) = ∑ i, p i * row i := by
    dsimp [col, row]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨j, i, ?_⟩
  change col j ≤ row i
  exact hj.trans (hswap.trans_le hi)
