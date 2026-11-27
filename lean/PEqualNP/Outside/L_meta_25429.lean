import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25429
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.and, [6, 2]⟩,
  ⟨.not, [7]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [3, 9]⟩,
  ⟨.or, [6, 10]⟩,
  ⟨.or, [2, 11]⟩,
  ⟨.and, [8, 12]⟩], 13⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25429

open PEqualNP.Outside.L_meta_25429 in
theorem PEqualNP.Outside.L_meta_25429 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (12832443 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
