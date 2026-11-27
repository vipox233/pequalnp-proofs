import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22770 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947629 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  refine ⟨(⟨[⟨.or, [3, 7]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [14, 9]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [4, 19]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [21, 22]⟩], 23⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
