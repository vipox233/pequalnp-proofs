import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_23658 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275390 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [4, 0]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [16, 11]⟩, ⟨.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
