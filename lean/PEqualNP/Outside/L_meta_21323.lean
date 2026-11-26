import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21323 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104283 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [4, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [5, 15]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [10, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
