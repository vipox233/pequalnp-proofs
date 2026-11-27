import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21906
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [6, 10]⟩], 11⟩
end PEqualNP.Outside.L_meta_21906

open PEqualNP.Outside.L_meta_21906 in
theorem PEqualNP.Outside.L_meta_21906 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33552 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
