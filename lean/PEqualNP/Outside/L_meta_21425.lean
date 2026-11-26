import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21425 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241338 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨.or, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [1, 14]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
