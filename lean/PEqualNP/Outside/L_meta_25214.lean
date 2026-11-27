import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25214 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34201 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [6, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 10] }], output := 15 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
