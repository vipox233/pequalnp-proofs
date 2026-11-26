import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21362 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39419 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨⟨[
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.and, [15, 13]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [19, 18]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
