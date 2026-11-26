import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19954 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3537932711340590220 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  let C : Circuit := ⟨[⟨.or, [5, 3]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [15, 6]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [14, 1]⟩, ⟨.or, [20, 8]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [25, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [24, 21]⟩, ⟨.and, [5, 23]⟩, ⟨.or, [3, 29]⟩, ⟨.or, [4, 13]⟩, ⟨.and, [28, 18]⟩, ⟨.or, [30, 20]⟩, ⟨.and, [32, 31]⟩, ⟨.or, [26, 1]⟩, ⟨.or, [24, 34]⟩, ⟨.and, [37, 36]⟩, ⟨.or, [27, 33]⟩, ⟨.or, [38, 35]⟩, ⟨.and, [5, 12]⟩, ⟨.or, [39, 40]⟩], 42⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
