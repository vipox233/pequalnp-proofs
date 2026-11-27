import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24405 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (49807 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.and, [11, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
