import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19761 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12848437582187957865 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  let C : Circuit := ⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [20, 18]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [28, 16]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [33, 16]⟩, ⟨.and, [5, 34]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩], 47⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
