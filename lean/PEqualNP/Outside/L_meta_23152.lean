import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_23152 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30456 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  let C : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [6, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
