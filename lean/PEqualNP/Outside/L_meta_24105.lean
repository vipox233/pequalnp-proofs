import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24105 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4441 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [8, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
