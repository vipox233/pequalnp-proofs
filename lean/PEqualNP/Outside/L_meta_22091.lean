import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22091 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17053 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [13, 10]⟩,
    ⟨.or, [14, 12]⟩,
    ⟨.not, [15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
