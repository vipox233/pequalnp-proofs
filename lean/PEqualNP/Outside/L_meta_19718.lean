import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19718_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [24, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [33, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [19, 28]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [20, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [21, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [23, 30]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 43]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 32]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [44, 45]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [26, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [46, 47]⟩], 48⟩

end PEqualNP.Outside.L_meta_19718_aux

theorem PEqualNP.Outside.L_meta_19718 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨PEqualNP.Outside.L_meta_19718_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19718_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
