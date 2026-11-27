import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21718 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283549 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [1]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.not, [3]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [13, 11]⟩,
    ⟨.or, [14, 12]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
