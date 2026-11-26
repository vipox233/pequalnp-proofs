import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19729 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9589595487171930210 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [19, 14]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [15, 17]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [28, 14]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 27]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
