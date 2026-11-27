import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24423 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52276 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [2, 9]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
