import PEqualNP.Defs

-- The answer is the circuit: AND and OR gates of fan-in two; the file checks the gate kinds, the gate count
-- and the value on every input with one row and one column on.
namespace PEqualNP.Outside.L_meta_19774
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [10, 20]⟩, ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [24, 18]⟩, ⟨GateOp.and, [1, 25]⟩, ⟨GateOp.or, [8, 17]⟩, ⟨GateOp.or, [27, 19]⟩, ⟨GateOp.and, [2, 28]⟩, ⟨GateOp.or, [15, 20]⟩, ⟨GateOp.and, [3, 30]⟩, ⟨GateOp.or, [9, 21]⟩, ⟨GateOp.and, [4, 32]⟩, ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.or, [34, 19]⟩, ⟨GateOp.and, [5, 35]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.or, [37, 17]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [13, 21]⟩, ⟨GateOp.and, [7, 40]⟩, ⟨GateOp.or, [23, 26]⟩, ⟨GateOp.or, [42, 29]⟩, ⟨GateOp.or, [43, 31]⟩, ⟨GateOp.or, [44, 33]⟩, ⟨GateOp.or, [45, 36]⟩, ⟨GateOp.or, [46, 39]⟩, ⟨GateOp.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 8 => (13555826764713151335 : ℕ).testBit (8 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_19774

theorem PEqualNP.Outside.L_meta_19774 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13555826764713151335 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19774.circ, PEqualNP.Outside.L_meta_19774.mono, by decide, PEqualNP.Outside.L_meta_19774.rep⟩
