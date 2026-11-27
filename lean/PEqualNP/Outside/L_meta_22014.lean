import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22014 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [4]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [14, 13]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
