import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19753 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6616700159142438735 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  let C : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [23, 21]⟩, ⟨.and, [0, 24]⟩, ⟨.or, [16, 22]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [30, 13]⟩, ⟨.or, [31, 19]⟩, ⟨.and, [3, 32]⟩, ⟨.or, [18, 22]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [36, 18]⟩, ⟨.and, [5, 37]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 38]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
