import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22951 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (8322555 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [23, 22] }], output := 24 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
