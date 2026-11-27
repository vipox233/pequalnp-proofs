import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22612_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [5, 6]⟩,
  ⟨.or, [0, 4]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [2, 11]⟩,
  ⟨.or, [1, 11]⟩,
  ⟨.or, [14, 15]⟩,
  ⟨.and, [17, 18]⟩,
  ⟨.and, [10, 16]⟩,
  ⟨.and, [12, 13]⟩,
  ⟨.or, [19, 20]⟩,
  ⟨.or, [22, 21]⟩], 23⟩

theorem monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22612_aux

theorem PEqualNP.Outside.L_meta_22612 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292606 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22612_aux.witness, PEqualNP.Outside.L_meta_22612_aux.monotone,
    by decide +kernel, by decide +kernel⟩
