import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21708 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275099 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

