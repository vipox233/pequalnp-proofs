import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22545 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940215 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [12, 13]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [21, 4]⟩], 22⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
