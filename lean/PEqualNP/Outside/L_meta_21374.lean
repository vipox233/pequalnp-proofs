import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21374 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103897 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨⟨[
    ⟨.or, [7, 8]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 18]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
