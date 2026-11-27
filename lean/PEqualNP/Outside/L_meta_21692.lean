import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21692 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25502 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

