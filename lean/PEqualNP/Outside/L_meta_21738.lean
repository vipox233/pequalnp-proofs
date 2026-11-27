import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21738
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [6, 13]⟩], 14⟩
end PEqualNP.Outside.L_meta_21738

open PEqualNP.Outside.L_meta_21738 in
theorem PEqualNP.Outside.L_meta_21738 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266322 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
