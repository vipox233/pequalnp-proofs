import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21914
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.and, [0, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [6, 11]⟩], 12⟩
end PEqualNP.Outside.L_meta_21914

open PEqualNP.Outside.L_meta_21914 in
theorem PEqualNP.Outside.L_meta_21914 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
