import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19793
def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [25, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 36]⟩], 43⟩
theorem valid : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_19793

theorem PEqualNP.Outside.L_meta_19793 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4868853174714768465 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_19793.witness, PEqualNP.Outside.L_meta_19793.valid, by decide, by decide +kernel⟩
