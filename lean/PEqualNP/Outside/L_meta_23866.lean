import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23866 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (5021 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [9, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
