import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21742 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266972 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.not, [15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
