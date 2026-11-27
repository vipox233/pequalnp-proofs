import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22611 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4062455 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 20] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
