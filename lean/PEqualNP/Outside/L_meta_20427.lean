import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20427 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3260509 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [2, 12]⟩,
    ⟨.or, [2, 13]⟩,
    ⟨.not, [15]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.and, [14, 17]⟩
  ], 18⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
