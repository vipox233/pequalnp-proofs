import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23491 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1854 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.and, [6, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
