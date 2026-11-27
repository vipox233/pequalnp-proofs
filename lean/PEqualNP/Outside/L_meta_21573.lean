import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21573 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17043935 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] }], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
