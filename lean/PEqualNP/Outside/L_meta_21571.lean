import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21571 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (287711 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [4]⟩,
    ⟨.and, [3, 5]⟩,
    ⟨.and, [2, 4]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [8, 6]⟩,
    ⟨.or, [9, 7]⟩
  ], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
