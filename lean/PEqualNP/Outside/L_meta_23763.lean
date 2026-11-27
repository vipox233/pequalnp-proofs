import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23763 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8787 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.or, [6, 9]⟩
  ], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
