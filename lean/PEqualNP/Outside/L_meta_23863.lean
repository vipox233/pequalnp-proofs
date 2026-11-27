import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23863
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [3, 4]⟩,
  ⟨.and, [1, 5]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.not, [7]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.or, [0, 9]⟩], 10⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23863

open PEqualNP.Outside.L_meta_23863 in
theorem PEqualNP.Outside.L_meta_23863 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4895 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
