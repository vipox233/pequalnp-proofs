import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23246 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (118463 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [8, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
