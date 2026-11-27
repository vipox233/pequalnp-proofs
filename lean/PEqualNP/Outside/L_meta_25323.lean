import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25323
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 2]⟩,
  ⟨.not, [4]⟩,
  ⟨.or, [6, 7]⟩,
  ⟨.and, [1, 2]⟩,
  ⟨.or, [3, 9]⟩,
  ⟨.and, [6, 10]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.not, [12]⟩,
  ⟨.or, [0, 13]⟩,
  ⟨.and, [8, 14]⟩], 15⟩

lemma valid : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25323

open PEqualNP.Outside.L_meta_25323 in
theorem PEqualNP.Outside.L_meta_25323 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180271 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨witness, valid, by decide, by decide +kernel⟩
