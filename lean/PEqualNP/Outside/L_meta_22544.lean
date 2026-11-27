import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22544 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940213 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : Circuit := ⟨[⟨.or, [1, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [10, 16]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [21, 4]⟩], 22⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
