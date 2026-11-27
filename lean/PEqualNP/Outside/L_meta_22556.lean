import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22556 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33719 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 10] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

