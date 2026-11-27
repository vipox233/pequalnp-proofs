import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21974 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (393 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }], output := 15 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
