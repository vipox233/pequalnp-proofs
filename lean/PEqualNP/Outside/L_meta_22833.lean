import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22833 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849774 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [0, 16]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [2, 14]⟩, ⟨.and, [3, 13]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [22, 20]⟩], 23⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
