import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21220 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241567 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨⟨[
    ⟨.or, [2, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [0, 17]⟩
  ], 18⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
