import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21287 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39806 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 17] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
