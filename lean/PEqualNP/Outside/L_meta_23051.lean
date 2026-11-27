import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23051 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948534 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 21]⟩,
    ⟨.and, [22, 16]⟩,
    ⟨.and, [23, 18]⟩,
    ⟨.and, [24, 20]⟩
  ], 25⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
