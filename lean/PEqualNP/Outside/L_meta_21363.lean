import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21363
open PEqualNP.CircuitLowerBounds

def circuit : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.and, [1, 5]⟩,
  ⟨.or, [10, 2]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [11, 7]⟩,
  ⟨.or, [9, 13]⟩,
  ⟨.or, [12, 6]⟩,
  ⟨.and, [15, 14]⟩,
  ⟨.or, [13, 8]⟩,
  ⟨.or, [17, 3]⟩,
  ⟨.and, [9, 18]⟩,
  ⟨.or, [16, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_21363

open PEqualNP.Outside.L_meta_21363 in
theorem PEqualNP.Outside.L_meta_21363 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40318 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
