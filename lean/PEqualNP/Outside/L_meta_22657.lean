import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22657 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841145 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [5, 0]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [15, 13]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [6, 20]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
