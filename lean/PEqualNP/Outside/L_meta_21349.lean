import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21349 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112606 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [11, 14]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [3, 12]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [18, 17]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
