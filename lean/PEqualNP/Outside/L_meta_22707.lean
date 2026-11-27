import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22707_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[
  ⟨.or, [6, 8]⟩,
  ⟨.or, [1, 10]⟩,
  ⟨.or, [2, 9]⟩,
  ⟨.or, [0, 7]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [12, 14]⟩,
  ⟨.or, [1, 14]⟩,
  ⟨.or, [11, 15]⟩,
  ⟨.or, [3, 6]⟩,
  ⟨.and, [16, 18]⟩,
  ⟨.and, [13, 17]⟩,
  ⟨.and, [11, 15]⟩,
  ⟨.or, [19, 20]⟩,
  ⟨.or, [22, 21]⟩], 23⟩

theorem monotone : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22707_aux

theorem PEqualNP.Outside.L_meta_22707 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904183 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22707_aux.witness, PEqualNP.Outside.L_meta_22707_aux.monotone,
    by decide +kernel, by decide +kernel⟩
