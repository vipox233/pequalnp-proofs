import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20328 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14523610048827323415 : ℕ).testBit (8 * u.val + v.val)) 29) := by
  refine ⟨⟨[
    ⟨.or, [2, 12]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [6, 14]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [1, 19]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [15, 28]⟩,
    ⟨.or, [3, 20]⟩,
    ⟨.or, [0, 15]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [31, 32]⟩,
    ⟨.or, [1, 17]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.and, [21, 22]⟩,
    ⟨.and, [23, 26]⟩,
    ⟨.and, [27, 29]⟩,
    ⟨.and, [30, 33]⟩,
    ⟨.and, [34, 35]⟩,
    ⟨.or, [36, 37]⟩,
    ⟨.or, [41, 38]⟩,
    ⟨.or, [42, 39]⟩,
    ⟨.or, [43, 40]⟩
  ], 44⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
