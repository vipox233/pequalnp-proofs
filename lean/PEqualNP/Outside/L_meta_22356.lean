import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22356 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841196 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [6, 8]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [4, 2]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [14, 13]⟩, ⟨.and, [17, 19]⟩, ⟨.and, [16, 18]⟩, ⟨.or, [21, 20]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
