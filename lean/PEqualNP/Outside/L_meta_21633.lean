import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21633
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 9]⟩], 10⟩
end PEqualNP.Outside.L_meta_21633

open PEqualNP.Outside.L_meta_21633 in
theorem PEqualNP.Outside.L_meta_21633 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (5020 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
