import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21975
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [1, 7]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.or, [4, 9]⟩,
  ⟨.not, [10]⟩,
  ⟨.and, [6, 11]⟩], 12⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21975

open PEqualNP.Outside.L_meta_21975 in
theorem PEqualNP.Outside.L_meta_21975 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (397 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
