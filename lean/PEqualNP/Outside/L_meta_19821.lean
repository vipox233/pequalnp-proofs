import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19821 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2278450633163008380 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  let C : Circuit := ⟨[⟨.or, [8, 14]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [23, 14]⟩, ⟨.or, [24, 18]⟩, ⟨.and, [0, 25]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [1, 27]⟩, ⟨.or, [19, 21]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [31, 21]⟩, ⟨.and, [3, 32]⟩, ⟨.or, [16, 22]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [18, 22]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [40, 18]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
