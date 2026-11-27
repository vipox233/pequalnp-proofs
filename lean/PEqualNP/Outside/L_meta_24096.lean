import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24096_aux
open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [5, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [8, 9]⟩], 10⟩

end PEqualNP.Outside.L_meta_24096_aux

theorem PEqualNP.Outside.L_meta_24096 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807641 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24096_aux.witness, ?_, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_24096_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
