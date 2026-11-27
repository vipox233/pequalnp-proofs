import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25995 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 7, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.and, [0, 7]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [3, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
  · decide
