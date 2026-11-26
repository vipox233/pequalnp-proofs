import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19726 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3537932711340590220 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [2, 11]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [14, 9]⟩, ⟨.or, [20, 5]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [3, 24]⟩, ⟨.or, [25, 22]⟩, ⟨.and, [24, 26]⟩, ⟨.or, [9, 28]⟩, ⟨.and, [21, 18]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [27, 29]⟩, ⟨.and, [33, 19]⟩, ⟨.and, [31, 23]⟩, ⟨.or, [32, 35]⟩, ⟨.and, [35, 24]⟩, ⟨.or, [8, 37]⟩, ⟨.or, [30, 34]⟩, ⟨.and, [7, 38]⟩, ⟨.or, [40, 36]⟩, ⟨.or, [37, 42]⟩], 43⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
