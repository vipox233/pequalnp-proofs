import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21132 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36316 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨⟨[⟨.or, [2, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [15, 12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [16, 17]⟩], 18⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
