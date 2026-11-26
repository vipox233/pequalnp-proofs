import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21296 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40796 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [5, 0]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [4, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
