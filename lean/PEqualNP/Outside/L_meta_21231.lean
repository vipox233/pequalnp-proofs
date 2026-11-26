import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21231 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (35255 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨⟨[
    ⟨.or, [0, 7]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.and, [12, 10]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [9, 14]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [18, 17]⟩
  ], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
