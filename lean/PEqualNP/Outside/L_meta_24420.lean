import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24420
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.not, [5]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.not, [4]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.or, [1, 10]⟩,
  ⟨.and, [7, 11]⟩], 12⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24420

open PEqualNP.Outside.L_meta_24420 in
theorem PEqualNP.Outside.L_meta_24420 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51119 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
