import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21112 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (35254 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := [
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 1] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 8] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 3] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 11] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 7] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 13] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 15] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] },
      { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }
    ], output := 18 }
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp [C, List.mem_cons] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide
  · decide
