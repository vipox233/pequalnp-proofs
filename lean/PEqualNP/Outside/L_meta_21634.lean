import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21634
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [7, 10]⟩], 11⟩
end PEqualNP.Outside.L_meta_21634

open PEqualNP.Outside.L_meta_21634 in
theorem PEqualNP.Outside.L_meta_21634 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (5021 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
