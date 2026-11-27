import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23058 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030205 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [15, 12]⟩,
    ⟨.and, [20, 17]⟩,
    ⟨.or, [21, 22]⟩
  ], 23⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
