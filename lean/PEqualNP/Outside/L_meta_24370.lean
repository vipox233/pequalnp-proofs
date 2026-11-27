import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24370 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274960319 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
