import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19757 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9891717104032518705 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [8, 15]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [8, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [21, 15]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [4, 28]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [5, 30]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [32, 14]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 29]⟩, ⟨.or, [40, 31]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
