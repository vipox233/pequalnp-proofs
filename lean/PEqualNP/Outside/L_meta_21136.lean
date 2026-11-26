import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_21136 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36798 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  let C : Circuit := ⟨[⟨.or, [2, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [14, 15]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
