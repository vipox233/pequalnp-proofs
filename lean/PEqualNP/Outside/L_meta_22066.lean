import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22066 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (188 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 15] }], output := 16 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
