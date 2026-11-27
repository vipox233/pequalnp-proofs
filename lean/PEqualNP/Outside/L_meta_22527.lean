import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22527 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16776 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.not, [12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
