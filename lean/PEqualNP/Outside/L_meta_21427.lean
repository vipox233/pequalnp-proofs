import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21427 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245629 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.and, [16, 11]⟩,
    ⟨.and, [13, 18]⟩,
    ⟨.or, [19, 20]⟩
  ], 21⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
