import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22697 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851253 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 13]⟩, ⟨.and, [18, 19]⟩, ⟨.and, [6, 2]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [17, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
