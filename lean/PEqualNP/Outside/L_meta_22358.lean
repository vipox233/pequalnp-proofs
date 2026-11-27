import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_22358 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841204 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨(⟨[⟨.or, [7, 4]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [15, 8]⟩, ⟨.and, [17, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [16, 2]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [21, 20]⟩], 22⟩ : Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
