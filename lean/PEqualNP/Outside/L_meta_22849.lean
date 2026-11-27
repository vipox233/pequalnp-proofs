import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22849 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904054 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }], output := 24 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
