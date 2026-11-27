import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22618 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325118 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 12]⟩, ⟨.and, [4, 13]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [11, 22]⟩], 23⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
