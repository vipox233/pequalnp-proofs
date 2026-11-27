import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25978 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 14, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [8, 4]⟩, ⟨.not, [9]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [11, 10]⟩], 12⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
  · decide
