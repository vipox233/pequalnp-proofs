import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23926 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (201 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [10, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
