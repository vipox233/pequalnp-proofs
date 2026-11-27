import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23404_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.not, [2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23404_aux

theorem PEqualNP.Outside.L_meta_23404 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (233147 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23404_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_23404_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
