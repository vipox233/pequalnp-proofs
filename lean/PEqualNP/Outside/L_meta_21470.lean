import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21470 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8606 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 4]⟩,
    ⟨.and, [0, 7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
