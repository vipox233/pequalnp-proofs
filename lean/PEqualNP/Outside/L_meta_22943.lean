import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22943 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2080638 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [18, 14]⟩,
    ⟨.and, [19, 16]⟩,
    ⟨.or, [20, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
