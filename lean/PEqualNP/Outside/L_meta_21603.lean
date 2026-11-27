import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21603 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (553823 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [1, 5]⟩, ⟨.not, [1]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [11, 9]⟩], 12⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
