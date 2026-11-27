import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22421 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881085 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [15, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [16, 0]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [21, 4]⟩], 22⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
