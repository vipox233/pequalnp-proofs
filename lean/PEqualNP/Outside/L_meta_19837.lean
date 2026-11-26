import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19837 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15680755338451602420 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  let C : Circuit := ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [22, 19]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [25, 18]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [28, 19]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [31, 20]⟩, ⟨.and, [3, 32]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
