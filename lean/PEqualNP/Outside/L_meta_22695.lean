import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22695 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849780 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [7, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [12, 11]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
