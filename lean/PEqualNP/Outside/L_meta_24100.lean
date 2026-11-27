import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_24100 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4369 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
