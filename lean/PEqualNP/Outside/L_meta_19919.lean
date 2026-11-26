import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19919_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [26, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [28, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 20]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [30, 31]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 21]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [32, 33]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 22]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 35]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 24]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [36, 37]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 25]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 39]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 27]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 41]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 29]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [42, 43]⟩], 44⟩

end PEqualNP.Outside.L_meta_19919_aux

theorem PEqualNP.Outside.L_meta_19919 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8125095274657465365 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  refine ⟨PEqualNP.Outside.L_meta_19919_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19919_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
