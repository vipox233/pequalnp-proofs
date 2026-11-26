import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20224
def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 23]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 26]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [31, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [34, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [38, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [33, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [44, 42]⟩], 45⟩
theorem valid : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_20224

theorem PEqualNP.Outside.L_meta_20224 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  exact ⟨PEqualNP.Outside.L_meta_20224.witness, PEqualNP.Outside.L_meta_20224.valid, by decide, by decide +kernel⟩
