import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20650 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15826944 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.or, [13, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
