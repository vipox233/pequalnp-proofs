import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23951 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4958 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 0]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 1]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 5]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 2]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 10]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
