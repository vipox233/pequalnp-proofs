import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20687 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14746656 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  try unfold PEqualNP.Represents.RepSizeAtMost
  try unfold PEqualNP.MetaComplexity.HasCircuitSize
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 16]⟩], 17⟩, ?_, ?_, ?_⟩
  all_goals first
    | (intro g hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
    | decide
    | (unfold PEqualNP.Represents.Represents; decide)
