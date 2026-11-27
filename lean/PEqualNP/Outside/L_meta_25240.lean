import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25240 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50343 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [4]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 10]⟩, ⟨.not, [9]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [8, 11]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
