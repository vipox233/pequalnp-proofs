import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22505 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898221 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [19, 8]⟩, ⟨.and, [20, 18]⟩, ⟨.or, [21, 4]⟩], 22⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
