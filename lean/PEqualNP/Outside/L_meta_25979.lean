import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25979 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [10, 11]⟩], 12⟩, ?_, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
