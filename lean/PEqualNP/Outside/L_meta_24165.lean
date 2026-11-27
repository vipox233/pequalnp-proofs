import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24165 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [0, 12]⟩,
    ⟨.or, [1, 13]⟩,
    ⟨.and, [10, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
