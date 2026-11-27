import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22851 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907183 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [0, 18]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [19, 16]⟩,
    ⟨.and, [22, 17]⟩,
    ⟨.and, [23, 21]⟩
  ], 24⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
