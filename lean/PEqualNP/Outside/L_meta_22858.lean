import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22858 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881966 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.and, [16, 15]⟩,
    ⟨.and, [22, 19]⟩,
    ⟨.and, [23, 21]⟩
  ], 24⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
