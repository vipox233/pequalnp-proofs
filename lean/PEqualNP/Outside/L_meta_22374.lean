import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22374 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841660 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [0, 12]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.and, [15, 13]⟩,
    ⟨.and, [19, 17]⟩,
    ⟨.and, [10, 18]⟩,
    ⟨.or, [20, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
