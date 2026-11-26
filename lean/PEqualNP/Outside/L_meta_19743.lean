import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19743_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [29, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [16, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [37, 38]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [39, 40]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [41, 42]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [43, 44]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [24, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [45, 46]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 36]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [47, 48]⟩], 49⟩

end PEqualNP.Outside.L_meta_19743_aux

theorem PEqualNP.Outside.L_meta_19743 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12606226115316667695 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  refine ⟨PEqualNP.Outside.L_meta_19743_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19743_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
