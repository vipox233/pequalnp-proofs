import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22710 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907246 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 18]⟩,
    ⟨.and, [15, 11]⟩,
    ⟨.and, [17, 19]⟩,
    ⟨.or, [20, 21]⟩
  ], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
