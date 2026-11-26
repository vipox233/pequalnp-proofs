import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22036 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816685 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [19, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
