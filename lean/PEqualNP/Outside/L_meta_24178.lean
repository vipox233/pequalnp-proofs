import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24178 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266838 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.not, [14]⟩,
    ⟨.and, [13, 15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
