import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25364 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2198074 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
