import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22698 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851257 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [0, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [12, 10]⟩, ⟨.and, [13, 3]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [5, 14]⟩, ⟨.and, [22, 21]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
