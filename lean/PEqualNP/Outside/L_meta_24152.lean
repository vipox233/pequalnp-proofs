import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24152
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [3, 4]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.and, [5, 6]⟩,
  ⟨.and, [0, 2]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.not, [10]⟩,
  ⟨.or, [7, 11]⟩], 12⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24152

open PEqualNP.Outside.L_meta_24152 in
theorem PEqualNP.Outside.L_meta_24152 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4889 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
