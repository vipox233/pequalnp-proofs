import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22523 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1838 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 5]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [9, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
