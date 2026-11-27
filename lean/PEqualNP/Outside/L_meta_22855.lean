import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22855 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1880958 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 23]⟩], 24⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
