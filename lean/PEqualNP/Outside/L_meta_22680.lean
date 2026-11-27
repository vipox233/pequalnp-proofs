import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22680 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843066 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [6, 0]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [5, 13]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [10, 17]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [11, 21]⟩, ⟨.or, [20, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
