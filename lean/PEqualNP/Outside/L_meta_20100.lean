import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20100 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14523610048827323415 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  refine ⟨⟨[
    ⟨.or, [3, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [16, 25]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [17, 27]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [23, 29]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [25, 31]⟩,
    ⟨.and, [8, 30]⟩,
    ⟨.and, [9, 24]⟩,
    ⟨.and, [10, 19]⟩,
    ⟨.and, [11, 22]⟩,
    ⟨.and, [12, 28]⟩,
    ⟨.and, [13, 32]⟩,
    ⟨.and, [14, 26]⟩,
    ⟨.and, [15, 20]⟩,
    ⟨.or, [33, 34]⟩,
    ⟨.or, [41, 35]⟩,
    ⟨.or, [42, 36]⟩,
    ⟨.or, [43, 37]⟩,
    ⟨.or, [44, 38]⟩,
    ⟨.or, [45, 39]⟩,
    ⟨.or, [46, 40]⟩
  ], 47⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
