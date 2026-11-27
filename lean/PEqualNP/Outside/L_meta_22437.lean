import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22437 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881464 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 20] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
