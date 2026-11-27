import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24965 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408097 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [5, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.not, [12]⟩,
    ⟨.and, [8, 13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
