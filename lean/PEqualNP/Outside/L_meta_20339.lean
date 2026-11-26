import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20339 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17056109459091738360 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  refine ⟨⟨[
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 18]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 21]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 23]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 24]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 26]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 27]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 27]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [29, 30]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 18]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [25, 33]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 14]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 24]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [22, 36]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [34, 37]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [35, 39]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 32]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [28, 41]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [31, 42]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [38, 43]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [40, 44]⟩
    ], 45⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
