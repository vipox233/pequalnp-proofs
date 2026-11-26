import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22294 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838774 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨⟨[⟨.or, [9, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [12, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [14, 11]⟩, ⟨.and, [12, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [18, 11]⟩, ⟨.and, [19, 17]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [15, 21]⟩], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
