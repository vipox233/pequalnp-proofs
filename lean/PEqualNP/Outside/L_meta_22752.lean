import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22752 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940148 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [1, 6]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [12, 8]⟩, ⟨.or, [15, 7]⟩, ⟨.and, [2, 16]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [14, 15]⟩, ⟨.and, [20, 11]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
