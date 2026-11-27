import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22731 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898094 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨⟨[⟨.or, [5, 6]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [15, 9]⟩, ⟨.and, [0, 16]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [22, 20]⟩], 23⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
