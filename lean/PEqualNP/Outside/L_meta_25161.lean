import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25161 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [0, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
