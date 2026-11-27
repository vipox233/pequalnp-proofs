import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22705 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904053 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [0, 16]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [2, 14]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [22, 20]⟩], 23⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
