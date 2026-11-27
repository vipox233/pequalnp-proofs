import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26385 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 0, 3, 28] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.or, [5, 6]⟩, ⟨.not, [10]⟩, ⟨.and, [3, 10]⟩,
    ⟨.and, [4, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
