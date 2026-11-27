import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24897 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2297663 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
