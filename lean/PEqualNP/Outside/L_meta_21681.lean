import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21681
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.not, [11]⟩], 12⟩
end PEqualNP.Outside.L_meta_21681

open PEqualNP.Outside.L_meta_21681 in
theorem PEqualNP.Outside.L_meta_21681 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4957 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  ·
    intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
