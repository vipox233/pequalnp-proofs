import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19956 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨⟨[
    ⟨.or, [2, 0]⟩,
    ⟨.or, [4, 1]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.or, [6, 2]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [18, 0]⟩,
    ⟨.or, [5, 17]⟩,
    ⟨.or, [21, 1]⟩,
    ⟨.or, [7, 20]⟩,
    ⟨.or, [23, 16]⟩,
    ⟨.or, [19, 23]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [24, 16]⟩,
    ⟨.or, [24, 22]⟩,
    ⟨.or, [24, 19]⟩,
    ⟨.or, [25, 16]⟩,
    ⟨.or, [25, 18]⟩,
    ⟨.and, [31, 8]⟩,
    ⟨.and, [28, 9]⟩,
    ⟨.and, [27, 10]⟩,
    ⟨.and, [29, 11]⟩,
    ⟨.and, [32, 12]⟩,
    ⟨.and, [33, 13]⟩,
    ⟨.and, [26, 14]⟩,
    ⟨.and, [30, 15]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [42, 36]⟩,
    ⟨.or, [43, 37]⟩,
    ⟨.or, [44, 38]⟩,
    ⟨.or, [45, 39]⟩,
    ⟨.or, [46, 40]⟩,
    ⟨.or, [47, 41]⟩
  ], 48⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
