import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22067 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16522 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [2, 1]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [12, 7]⟩,
    ⟨.or, [13, 10]⟩,
    ⟨.or, [14, 11]⟩,
    ⟨.not, [15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
