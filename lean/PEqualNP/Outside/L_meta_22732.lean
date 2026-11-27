import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22732 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898102 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [4, 0]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [11, 10]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [12, 18]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [1, 20]⟩, ⟨.and, [19, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
