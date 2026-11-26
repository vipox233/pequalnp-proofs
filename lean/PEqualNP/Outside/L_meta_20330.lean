import PEqualNP.Defs

-- Circuit transported by a bipartite graph isomorphism from upstream public contribution PR26821.
theorem PEqualNP.Outside.L_meta_20330 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1892380200682152600 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [12, 1]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [11, 20]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [14, 23]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [25, 22]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [26, 2]⟩, ⟨.or, [28, 8]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [29, 31]⟩, ⟨.or, [17, 9]⟩, ⟨.and, [27, 30]⟩, ⟨.and, [24, 4]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [32, 36]⟩, ⟨.or, [38, 37]⟩], 39⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
