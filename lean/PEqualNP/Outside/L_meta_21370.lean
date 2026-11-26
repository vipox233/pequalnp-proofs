import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21370 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103678 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 16]⟩,
    ⟨.and, [15, 11]⟩,
    ⟨.and, [10, 17]⟩,
    ⟨.or, [18, 19]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
