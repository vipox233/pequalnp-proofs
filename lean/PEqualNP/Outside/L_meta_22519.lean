import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22519 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900155 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [10, 13]⟩,
    ⟨.and, [11, 14]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [4, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
