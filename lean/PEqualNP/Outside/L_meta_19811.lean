import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19811 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨⟨[
    ⟨.or, [8, 12]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [22, 14]⟩,
    ⟨.or, [23, 17]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.or, [9, 20]⟩,
    ⟨.and, [1, 26]⟩,
    ⟨.or, [11, 20]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [15, 21]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.or, [34, 18]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [37, 19]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [12, 21]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [25, 27]⟩,
    ⟨.or, [42, 29]⟩,
    ⟨.or, [43, 31]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 39]⟩,
    ⟨.or, [47, 41]⟩
  ], 48⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
