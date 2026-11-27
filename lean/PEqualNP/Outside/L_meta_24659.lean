import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24659 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (283332031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [7, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 9] }], output := 13 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
