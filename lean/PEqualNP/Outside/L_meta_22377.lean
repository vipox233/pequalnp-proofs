import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22377 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841717 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨.and, [0, 9]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [21, 4]⟩], 22⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
