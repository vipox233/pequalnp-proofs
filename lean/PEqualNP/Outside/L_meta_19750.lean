import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19750 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5360062095110517900 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨(⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [11, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [21, 13]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [26, 15]⟩, ⟨.and, [3, 27]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [14, 18]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [11, 17]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 28]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
