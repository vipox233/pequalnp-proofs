import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24160
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 4]⟩,
  ⟨.and, [0, 5]⟩,
  ⟨.and, [1, 4]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.and, [2, 3]⟩,
  ⟨.or, [5, 9]⟩,
  ⟨.not, [10]⟩,
  ⟨.and, [8, 11]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.or, [6, 13]⟩], 14⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24160

open PEqualNP.Outside.L_meta_24160 in
theorem PEqualNP.Outside.L_meta_24160 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266782 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
