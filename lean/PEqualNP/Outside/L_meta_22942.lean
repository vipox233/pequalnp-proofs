import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22942 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1949501 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨⟨[⟨.or, [5, 4]⟩, ⟨.or, [10, 6]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [6, 18]⟩, ⟨.and, [16, 19]⟩, ⟨.or, [15, 20]⟩, ⟨.or, [12, 21]⟩, ⟨.and, [4, 0]⟩, ⟨.or, [22, 23]⟩], 24⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
