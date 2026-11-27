import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22654 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840694 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 10]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 19]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 20]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 22]⟩], 23⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
