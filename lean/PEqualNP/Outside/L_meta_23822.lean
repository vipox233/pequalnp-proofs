import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23822
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [1, 6]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.not, [8]⟩,
  ⟨.and, [5, 9]⟩], 10⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23822

open PEqualNP.Outside.L_meta_23822 in
theorem PEqualNP.Outside.L_meta_23822 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (205 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
