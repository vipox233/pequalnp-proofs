import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25166

open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25166

theorem PEqualNP.Outside.L_meta_25166 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_25166.witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_25166.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
