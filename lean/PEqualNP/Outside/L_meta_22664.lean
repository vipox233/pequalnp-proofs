import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22664 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841519 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 22] }], output := 23 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
