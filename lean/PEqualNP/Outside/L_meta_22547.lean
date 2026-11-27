import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22547 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947515 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
