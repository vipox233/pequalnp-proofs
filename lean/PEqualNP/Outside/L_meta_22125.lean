import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22125 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837107 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [0, 14]⟩, ⟨.and, [1, 13]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
