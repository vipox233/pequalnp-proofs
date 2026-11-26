import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22038_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [1, 5]⟩,
  ⟨.or, [0, 4]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.or, [2, 7]⟩,
  ⟨.or, [3, 13]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.and, [6, 13]⟩,
  ⟨.and, [14, 15]⟩,
  ⟨.and, [12, 16]⟩,
  ⟨.or, [17, 18]⟩,
  ⟨.or, [20, 19]⟩], 21⟩

theorem monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22038_aux

theorem PEqualNP.Outside.L_meta_22038 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816746 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_22038_aux.witness, PEqualNP.Outside.L_meta_22038_aux.monotone,
    by decide +kernel, by decide +kernel⟩
