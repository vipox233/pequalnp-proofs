import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22869 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881974 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  try unfold PEqualNP.Represents.RepSizeAtMost
  try unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 23]⟩], 24⟩, ?_, ?_, ?_⟩
  all_goals first
    | (intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    | decide
    | (unfold PEqualNP.Represents.Represents; decide)
