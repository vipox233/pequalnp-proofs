import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21396
open PEqualNP.CircuitLowerBounds

def circuit : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.and, [1, 5]⟩,
  ⟨.or, [11, 9]⟩,
  ⟨.or, [10, 5]⟩,
  ⟨.or, [12, 13]⟩,
  ⟨.or, [13, 8]⟩,
  ⟨.and, [12, 15]⟩,
  ⟨.or, [16, 6]⟩,
  ⟨.or, [17, 7]⟩,
  ⟨.or, [18, 3]⟩,
  ⟨.and, [14, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_21396

open PEqualNP.Outside.L_meta_21396 in
theorem PEqualNP.Outside.L_meta_21396 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112126 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro gate hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
