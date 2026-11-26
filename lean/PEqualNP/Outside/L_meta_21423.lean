import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21423 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114622 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 12]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [17, 14]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [18, 19]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
