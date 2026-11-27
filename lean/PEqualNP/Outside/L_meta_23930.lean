import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23930
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 3]⟩,
  ⟨.and, [1, 3]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.not, [7]⟩,
  ⟨.and, [5, 8]⟩,
  ⟨.or, [4, 9]⟩,
  ⟨.not, [10]⟩], 11⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23930

open PEqualNP.Outside.L_meta_23930 in
theorem PEqualNP.Outside.L_meta_23930 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4367 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
