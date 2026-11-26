import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21369 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (48894 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [14, 17]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
