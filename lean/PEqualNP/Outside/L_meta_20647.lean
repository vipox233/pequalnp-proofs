import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20647 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (11763712 : ℕ).testBit (5 * u.val + v.val)) 6 := by
  exact ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), by simp [PEqualNP.MetaComplexity.Monotone2], by decide, by decide +kernel⟩
