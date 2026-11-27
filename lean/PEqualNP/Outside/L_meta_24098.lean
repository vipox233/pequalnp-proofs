import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24098 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4184 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [6, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
