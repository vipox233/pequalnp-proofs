import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22535 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18367 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [5]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [12, 11]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
