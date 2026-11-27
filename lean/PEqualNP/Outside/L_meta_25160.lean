import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25160 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16914 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
