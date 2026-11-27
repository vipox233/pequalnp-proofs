import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23229
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.not, [8]⟩,
  ⟨.and, [7, 9]⟩], 10⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23229

open PEqualNP.Outside.L_meta_23229 in
theorem PEqualNP.Outside.L_meta_23229 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50063 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
