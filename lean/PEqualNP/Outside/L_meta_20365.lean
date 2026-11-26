import PEqualNP.Defs

-- Circuit transported by a bipartite graph isomorphism from upstream public contribution PR26821.
theorem PEqualNP.Outside.L_meta_20365 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [8, 6]⟩, ⟨.or, [16, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [12, 20]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [13, 23]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [25, 22]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [26, 0]⟩, ⟨.or, [28, 11]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [29, 31]⟩, ⟨.or, [17, 10]⟩, ⟨.and, [27, 30]⟩, ⟨.and, [24, 2]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [32, 36]⟩, ⟨.or, [38, 37]⟩], 39⟩
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
