import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22337 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18361 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 16] }], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
