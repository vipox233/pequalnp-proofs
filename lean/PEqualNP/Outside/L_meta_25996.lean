import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25996 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 10, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [13]⟩, ⟨.or, [12, 14]⟩], 15⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
