import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21342 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112117 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 15]⟩,
    ⟨.and, [9, 14]⟩,
    ⟨.and, [16, 11]⟩,
    ⟨.or, [17, 18]⟩
  ], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
