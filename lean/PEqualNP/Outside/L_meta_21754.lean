import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21754 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283358 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [3]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.not, [3]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [14, 12]⟩,
    ⟨.or, [15, 13]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
