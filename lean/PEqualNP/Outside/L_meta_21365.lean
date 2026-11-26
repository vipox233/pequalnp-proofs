import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21365 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40411 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
