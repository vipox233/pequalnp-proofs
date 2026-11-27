import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22441 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881905 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [3, 7]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [16, 15]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [19, 0]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [20, 21]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
