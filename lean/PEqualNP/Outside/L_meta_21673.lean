import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21673
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [5, 9]⟩], 10⟩
end PEqualNP.Outside.L_meta_21673

open PEqualNP.Outside.L_meta_21673 in
theorem PEqualNP.Outside.L_meta_21673 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274910 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
