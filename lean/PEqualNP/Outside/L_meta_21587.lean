import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21587_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.not, [4]⟩, ⟨.and, [0, 5]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 7]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [10, 9]⟩, ⟨.not, [11]⟩], 12⟩

end PEqualNP.Outside.L_meta_21587_aux

theorem PEqualNP.Outside.L_meta_21587 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266704 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21587_aux.witness, ?_, by decide, by decide +kernel⟩
  intro gate hg
  simp only [PEqualNP.Outside.L_meta_21587_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
