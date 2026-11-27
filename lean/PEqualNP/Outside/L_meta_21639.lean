import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21639 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8661 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.not, [5]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [12, 11]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
