import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24987 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (12783423 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
