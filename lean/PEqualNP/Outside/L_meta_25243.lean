import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25243 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50604 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [5, 3]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [6, 0]⟩, ⟨.not, [8]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [9, 1]⟩, ⟨.not, [10]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
