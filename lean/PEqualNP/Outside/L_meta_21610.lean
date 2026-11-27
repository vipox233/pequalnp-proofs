import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21610 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (201 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [5, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, C]
  · decide
