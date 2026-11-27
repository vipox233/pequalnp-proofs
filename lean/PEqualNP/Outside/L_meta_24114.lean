import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24114 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13081 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.and, [2, 6]⟩,
      ⟨.or, [1, 7]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [5, 9]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.and, [1, 11]⟩,
      ⟨.or, [10, 12]⟩], 13⟩
  refine ⟨C, ?_, by decide +kernel, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
