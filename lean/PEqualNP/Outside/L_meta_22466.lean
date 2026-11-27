import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22466
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [3, 8]⟩,
  ⟨.and, [7, 9]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.or, [0, 11]⟩,
  ⟨.not, [12]⟩,
  ⟨.or, [10, 13]⟩,
  ⟨.or, [6, 14]⟩], 15⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22466

open PEqualNP.Outside.L_meta_22466 in
theorem PEqualNP.Outside.L_meta_22466 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20026 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
