import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21551 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8592 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [0, 4]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [9, 8]⟩
  ], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
