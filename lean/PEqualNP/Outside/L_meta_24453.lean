import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24453 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101039 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [11, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
