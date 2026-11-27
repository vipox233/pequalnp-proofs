import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21682
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [5, 11]⟩], 12⟩
end PEqualNP.Outside.L_meta_21682

open PEqualNP.Outside.L_meta_21682 in
theorem PEqualNP.Outside.L_meta_21682 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8785 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
