import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24361 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843965 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
