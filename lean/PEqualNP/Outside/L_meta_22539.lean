import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22539 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33559 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [3, 5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 11]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
