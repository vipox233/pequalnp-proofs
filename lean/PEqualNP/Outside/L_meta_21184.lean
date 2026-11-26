import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21184 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103903 : ℕ).testBit (5 * u.val + v.val)) 9) := by
  try unfold PEqualNP.Represents.RepSizeAtMost
  try unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩], 17⟩, ?_, ?_, ?_⟩
  all_goals first
    | (intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    | decide
    | (unfold PEqualNP.Represents.Represents; decide)
