import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21595 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275101 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [2, 4]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.not, [11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
