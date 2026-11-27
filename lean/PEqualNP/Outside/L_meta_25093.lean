import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25093 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843811 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
