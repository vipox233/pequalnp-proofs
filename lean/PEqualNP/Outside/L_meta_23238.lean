import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23238 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100159 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [1, 2]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [6, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
