import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24844 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2166588 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
