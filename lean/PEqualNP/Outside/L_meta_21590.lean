import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21590 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266967 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 11] }], output := 12 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
