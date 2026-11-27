import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22370 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841590 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.and, [16, 18]⟩,
    ⟨.and, [14, 12]⟩,
    ⟨.or, [19, 20]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
