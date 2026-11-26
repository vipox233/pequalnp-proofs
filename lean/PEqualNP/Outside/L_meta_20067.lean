import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20067 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12762594853557972675 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨⟨[
    ⟨.or, [0, 3]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 16]⟩,
    ⟨.or, [6, 17]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [0, 20]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [14, 24]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [10, 28]⟩,
    ⟨.or, [15, 25]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [18, 27]⟩,
    ⟨.and, [19, 33]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.and, [22, 32]⟩,
    ⟨.or, [36, 37]⟩,
    ⟨.and, [21, 26]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [40, 41]⟩,
    ⟨.and, [23, 30]⟩,
    ⟨.or, [42, 43]⟩,
    ⟨.and, [6, 29]⟩,
    ⟨.or, [44, 45]⟩], 46⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
