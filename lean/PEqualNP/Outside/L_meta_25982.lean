import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25982 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 7, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [0, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [4, 9]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [13, 15]⟩], 16⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
