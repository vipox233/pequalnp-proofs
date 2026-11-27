import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26022 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 13, 11, 7] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
