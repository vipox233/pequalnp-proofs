import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21953
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [2, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩
end PEqualNP.Outside.L_meta_21953

open PEqualNP.Outside.L_meta_21953 in
theorem PEqualNP.Outside.L_meta_21953 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33694 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
