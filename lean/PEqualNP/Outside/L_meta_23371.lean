import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23371 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (53055 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [1, 7]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [10, 11]⟩
  ], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
