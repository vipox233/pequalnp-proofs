import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25994 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 7, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨({ gates := [
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [8, 9] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 7] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 11] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [2] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 13] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 12] },
    { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 14] }], output := 16 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
