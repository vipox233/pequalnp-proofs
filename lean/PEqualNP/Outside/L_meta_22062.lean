import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22062 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33968 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 13] }], output := 15 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
