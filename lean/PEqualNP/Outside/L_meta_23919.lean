import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23919 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17043663 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩,
            ⟨.or, [0, 5]⟩,
            ⟨.or, [3, 6]⟩,
            ⟨.and, [4, 7]⟩,
            ⟨.and, [3, 5]⟩,
            ⟨.or, [8, 9]⟩,
            ⟨.not, [10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, or_imp, forall_and]
  · intro i j
    fin_cases i <;> fin_cases j <;> decide
