import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24502 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147475 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.not, [4]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [10, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
