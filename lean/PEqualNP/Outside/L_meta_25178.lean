import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25178 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17330 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [3, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [6, 10]⟩, ⟨.not, [12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
