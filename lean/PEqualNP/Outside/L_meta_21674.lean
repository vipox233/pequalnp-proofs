import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21674
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩], 13⟩
end PEqualNP.Outside.L_meta_21674

open PEqualNP.Outside.L_meta_21674 in
theorem PEqualNP.Outside.L_meta_21674 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275031 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
