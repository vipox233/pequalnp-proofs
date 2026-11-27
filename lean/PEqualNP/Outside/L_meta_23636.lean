import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23636 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275254 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 19] }], output := 20 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
