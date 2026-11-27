import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24692 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (444 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [10, 12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
