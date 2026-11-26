import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21384 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106298 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }], output := 20 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
