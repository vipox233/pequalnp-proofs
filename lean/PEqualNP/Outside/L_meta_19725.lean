import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19725 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8992515997758798780 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  let C : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [18, 22]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [25, 18]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [28, 21]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [16, 22]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [35, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 42]⟩], 49⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [C, Monotone2]
  · decide +kernel
