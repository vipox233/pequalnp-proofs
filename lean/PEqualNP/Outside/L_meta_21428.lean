import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_21428 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112382 : ℕ).testBit (5 * u.val + v.val)) 14 := by
  let C : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [7, 15]⟩, ⟨.and, [12, 16]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [18, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [14, 21]⟩], 22⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
