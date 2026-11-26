import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22132 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838909 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨⟨[⟨.or, [7, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 17]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [12, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
