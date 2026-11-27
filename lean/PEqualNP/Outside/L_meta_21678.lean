import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21678 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4894 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 3]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [14, 13]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
