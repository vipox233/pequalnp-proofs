import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22854 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908286 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.and, [14, 17]⟩,
    ⟨.and, [12, 19]⟩,
    ⟨.or, [20, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
