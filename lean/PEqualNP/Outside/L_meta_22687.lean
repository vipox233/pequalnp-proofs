import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22687 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843194 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [2, 8]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [3, 15]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [12, 11]⟩, ⟨.and, [4, 18]⟩, ⟨.or, [21, 20]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
