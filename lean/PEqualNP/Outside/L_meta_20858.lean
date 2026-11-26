import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20858 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27396129 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [10, 5]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [14, 9]⟩,
    ⟨.and, [4, 15]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [17, 13]⟩,
    ⟨.or, [18, 16]⟩
  ], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
