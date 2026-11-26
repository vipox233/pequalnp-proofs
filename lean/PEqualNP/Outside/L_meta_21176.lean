import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_21176 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103672 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  let C : Circuit := ⟨[⟨.or, [4, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
