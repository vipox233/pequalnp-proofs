import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22616 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323003 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [21, 22]⟩], 23⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
