import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24970 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408623 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [8]⟩, ⟨.not, [9]⟩, ⟨.and, [6, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
