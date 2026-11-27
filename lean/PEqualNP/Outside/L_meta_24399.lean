import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24399 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (140 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
