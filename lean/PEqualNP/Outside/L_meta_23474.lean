import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23474 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (412 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [10, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
