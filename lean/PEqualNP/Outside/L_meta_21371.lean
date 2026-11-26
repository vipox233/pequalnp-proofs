import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21371
open PEqualNP.CircuitLowerBounds

def circuit : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 8]⟩,
  ⟨.and, [9, 7]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [10, 13]⟩,
  ⟨.or, [13, 11]⟩,
  ⟨.and, [10, 15]⟩,
  ⟨.or, [12, 16]⟩,
  ⟨.or, [6, 3]⟩,
  ⟨.and, [14, 18]⟩,
  ⟨.or, [17, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_21371

open PEqualNP.Outside.L_meta_21371 in
theorem PEqualNP.Outside.L_meta_21371 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103742 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
