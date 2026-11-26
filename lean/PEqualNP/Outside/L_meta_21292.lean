import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21292 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40442 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [4, 0]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [13, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
