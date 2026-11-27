import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25383 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375359 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
