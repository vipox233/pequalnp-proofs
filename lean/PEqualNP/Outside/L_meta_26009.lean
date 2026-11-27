import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26009 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 12, 3, 3] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
     ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 1]⟩,
     ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩,
     ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩,
     ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9, 11]⟩,
     ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 11]⟩], 13⟩,
   by
     intro g hg
     fin_cases hg <;> exact ⟨by simp, by decide⟩,
   by decide, by decide, by decide⟩
