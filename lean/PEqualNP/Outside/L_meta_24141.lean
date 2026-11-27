import PEqualNP.Defs

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24141 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279517 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨(⟨[
      ⟨.and, [0, 1]⟩,
      ⟨.or, [2, 4]⟩,
      ⟨.and, [2, 4]⟩,
      ⟨.or, [1, 7]⟩,
      ⟨.or, [0, 8]⟩,
      ⟨.not, [9]⟩,
      ⟨.and, [6, 10]⟩,
      ⟨.or, [5, 11]⟩,
      ⟨.not, [12]⟩],
    13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
