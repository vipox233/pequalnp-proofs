import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22460
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [1, 3]⟩,
  ⟨.and, [2, 8]⟩,
  ⟨.or, [5, 9]⟩,
  ⟨.or, [4, 10]⟩,
  ⟨.or, [0, 11]⟩,
  ⟨.and, [6, 12]⟩,
  ⟨.not, [13]⟩,
  ⟨.and, [7, 14]⟩], 15⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22460

open PEqualNP.Outside.L_meta_22460 in
theorem PEqualNP.Outside.L_meta_22460 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17081 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
