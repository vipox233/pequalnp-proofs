import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22954 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1884030 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [16, 12]⟩,
    ⟨.and, [19, 14]⟩,
    ⟨.or, [20, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
