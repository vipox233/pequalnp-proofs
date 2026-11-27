import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21691 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13082 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [10, 4]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [14, 13]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
