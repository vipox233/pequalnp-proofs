import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22875 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883518 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [1, 5]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [19, 12]⟩,
    ⟨.and, [16, 14]⟩,
    ⟨.or, [20, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
