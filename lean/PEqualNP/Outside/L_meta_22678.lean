import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22678 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (842998 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [7, 1]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [5, 2]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [14, 12]⟩, ⟨.and, [16, 19]⟩, ⟨.and, [14, 5]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [20, 18]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
