import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22436 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881452 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[
    ⟨.or, [1, 7]⟩,
    ⟨.and, [6, 3]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [12, 4]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [14, 8]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.and, [10, 16]⟩,
    ⟨.or, [5, 13]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [14, 19]⟩,
    ⟨.and, [18, 20]⟩,
    ⟨.or, [17, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
