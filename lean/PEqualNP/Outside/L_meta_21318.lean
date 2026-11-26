import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21318 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103902 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨⟨[
    ⟨.or, [3, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.and, [14, 9]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [18, 17]⟩
  ], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
