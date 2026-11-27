import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23838 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4313 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 5]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.not, [9]⟩,
    ⟨.or, [8, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
