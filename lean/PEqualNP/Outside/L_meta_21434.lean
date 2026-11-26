import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21434 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241598 : ℕ).testBit (5 * u.val + v.val)) 15) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [17, 22] }], output := 23 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
