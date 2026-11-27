import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22894 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940149 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.and, [0, 16]⟩,
    ⟨.and, [10, 19]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [23, 22]⟩
  ], 24⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
