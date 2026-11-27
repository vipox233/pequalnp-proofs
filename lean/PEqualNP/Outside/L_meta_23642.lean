import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23642 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275324 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [3, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [2, 18]⟩, ⟨.and, [14, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
