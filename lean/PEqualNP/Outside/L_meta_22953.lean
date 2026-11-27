import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22953 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881982 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [0, 17]⟩, ⟨.and, [1, 16]⟩, ⟨.and, [2, 15]⟩, ⟨.and, [3, 14]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [23, 21]⟩], 24⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
