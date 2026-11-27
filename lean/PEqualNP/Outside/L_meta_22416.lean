import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22416 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (917309 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩], 22⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
