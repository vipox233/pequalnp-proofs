import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22666 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841527 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 22] }], output := 23 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
