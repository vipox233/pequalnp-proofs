import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25954 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 7, 0, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩], 10⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
  · decide +kernel
