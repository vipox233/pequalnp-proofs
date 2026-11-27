import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23628 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274873 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 19] }], output := 20 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
