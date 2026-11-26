import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19745 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10692751789718129190 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [8, 11]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [9, 17]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [21, 14]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [26, 15]⟩, ⟨.and, [3, 27]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 28]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
