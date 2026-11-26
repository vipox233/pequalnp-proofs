import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_21209 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112540 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨(⟨[⟨.or, [6, 7]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [5, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [11, 17]⟩], 18⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
