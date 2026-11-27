import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23153 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30457 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 17] }], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
