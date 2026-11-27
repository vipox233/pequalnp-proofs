import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22393 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849719 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
