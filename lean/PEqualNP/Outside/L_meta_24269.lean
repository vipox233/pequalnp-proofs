import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24269 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16959 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [6, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
