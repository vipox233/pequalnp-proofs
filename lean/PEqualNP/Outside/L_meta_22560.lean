import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22560 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947644 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 20] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

