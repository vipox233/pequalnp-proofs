import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25205 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33941 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
