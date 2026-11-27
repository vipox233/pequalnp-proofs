import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25986 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 13, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide
  · decide +kernel
