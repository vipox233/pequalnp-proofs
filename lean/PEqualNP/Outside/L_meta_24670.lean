import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24670 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630322079 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.not, [12]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
