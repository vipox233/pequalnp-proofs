import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22538 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33558 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

