import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21719
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.and, [4, 6]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [2, 4]⟩,
  ⟨.and, [3, 9]⟩,
  ⟨.not, [10]⟩,
  ⟨.and, [8, 11]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.or, [5, 13]⟩], 14⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21719

open PEqualNP.Outside.L_meta_21719 in
theorem PEqualNP.Outside.L_meta_21719 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283550 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
