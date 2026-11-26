import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19829 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14134136632318694985 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [8, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [19, 14]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [6, 32]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [34, 15]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 33]⟩, ⟨.or, [42, 36]⟩], 43⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
