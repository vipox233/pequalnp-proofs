import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20119 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6623703746638232805 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨⟨[⟨.or, [13, 15]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [17, 11]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [20, 11]⟩, ⟨.or, [21, 12]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [18, 8]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [19, 25]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [11, 24]⟩, ⟨.or, [16, 24]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [31, 10]⟩, ⟨.or, [32, 13]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [29, 10]⟩, ⟨.and, [5, 35]⟩, ⟨.and, [0, 28]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [14, 21]⟩, ⟨.and, [6, 39]⟩, ⟨.or, [17, 29]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [37, 23]⟩, ⟨.or, [27, 43]⟩, ⟨.or, [44, 38]⟩, ⟨.or, [45, 42]⟩, ⟨.or, [46, 36]⟩, ⟨.or, [47, 40]⟩, ⟨.or, [48, 34]⟩], 49⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
