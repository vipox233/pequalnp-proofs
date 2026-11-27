import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22260 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (818814 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [18, 8]⟩, ⟨.and, [19, 15]⟩, ⟨.or, [20, 16]⟩], 21⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
