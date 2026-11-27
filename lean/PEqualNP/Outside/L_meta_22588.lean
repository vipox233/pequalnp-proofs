import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22588 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (917 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }], output := 14 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
