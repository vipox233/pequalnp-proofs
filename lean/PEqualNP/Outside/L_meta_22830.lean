import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22830 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843134 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [22, 23] }], output := 24 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
