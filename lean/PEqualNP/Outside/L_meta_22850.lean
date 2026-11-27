import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22850 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904055 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [5, 18]⟩,
    ⟨.and, [19, 15]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.and, [0, 17]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [23, 22]⟩
  ], 24⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
