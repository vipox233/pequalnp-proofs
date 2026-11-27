import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24742 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100139 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [7, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
