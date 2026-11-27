import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22709 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907181 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 22] }], output := 23 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
