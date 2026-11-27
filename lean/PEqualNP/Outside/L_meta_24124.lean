import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24124 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266903 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 13] }], output := 14 }, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
