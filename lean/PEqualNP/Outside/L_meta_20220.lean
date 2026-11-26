import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20220 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16472541325419705030 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  refine ⟨⟨[
    ⟨.or, [6, 14]⟩,
    ⟨.or, [2, 13]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [15, 26]⟩,
    ⟨.or, [27, 28]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [19, 30]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.or, [17, 32]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [9, 34]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [21, 24]⟩,
    ⟨.and, [25, 29]⟩,
    ⟨.and, [31, 33]⟩,
    ⟨.and, [35, 36]⟩,
    ⟨.or, [37, 38]⟩,
    ⟨.or, [41, 39]⟩,
    ⟨.or, [42, 40]⟩
  ], 43⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
