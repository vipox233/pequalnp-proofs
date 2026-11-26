import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21272 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39255 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
      ⟨.or, [2, 0]⟩,
      ⟨.or, [4, 1]⟩,
      ⟨.or, [10, 9]⟩,
      ⟨.and, [6, 9]⟩,
      ⟨.or, [5, 12]⟩,
      ⟨.or, [7, 0]⟩,
      ⟨.or, [8, 10]⟩,
      ⟨.and, [15, 14]⟩,
      ⟨.or, [13, 16]⟩,
      ⟨.or, [3, 17]⟩,
      ⟨.and, [18, 11]⟩], 19⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
