import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25421

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.not, [5]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [7, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25421

theorem PEqualNP.Outside.L_meta_25421 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6524861 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25421.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_25421.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
