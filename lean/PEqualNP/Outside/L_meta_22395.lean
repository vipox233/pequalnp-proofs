import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22395 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849783 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨{ gates := [⟨.or, [5, 1]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [17, 7]⟩, ⟨.and, [18, 15]⟩, ⟨.and, [16, 13]⟩, ⟨.or, [19, 4]⟩, ⟨.or, [21, 20]⟩], output := 22 }, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
