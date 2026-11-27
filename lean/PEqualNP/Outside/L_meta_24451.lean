import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24451 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100923 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 10] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide +kernel⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
