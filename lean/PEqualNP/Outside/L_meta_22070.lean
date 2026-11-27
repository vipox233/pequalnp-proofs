import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22070 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16827 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [15] }], output := 16 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
