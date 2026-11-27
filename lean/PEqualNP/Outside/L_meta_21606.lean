import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21606 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17052113 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [8, 3]⟩,
    ⟨.and, [4, 9]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.not, [11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
