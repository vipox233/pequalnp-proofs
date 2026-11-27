import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25946 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
