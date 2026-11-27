import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22692 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849709 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
