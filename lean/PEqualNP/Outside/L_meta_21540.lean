import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21540 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (405 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨{ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }], output := 10 }, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
