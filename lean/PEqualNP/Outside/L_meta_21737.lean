import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21737
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [5, 13]⟩, ⟨.not, [14]⟩], 15⟩
end PEqualNP.Outside.L_meta_21737

open PEqualNP.Outside.L_meta_21737 in
theorem PEqualNP.Outside.L_meta_21737 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266321 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
