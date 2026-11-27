import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22829 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841718 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨.or, [4, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [0, 16]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [3, 14]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [22, 20]⟩], 23⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
