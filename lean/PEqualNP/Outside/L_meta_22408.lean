import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22408 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907134 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [0, 16]⟩,
    ⟨.or, [9, 17]⟩,
    ⟨.or, [4, 18]⟩,
    ⟨.and, [19, 20]⟩,
    ⟨.or, [13, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
