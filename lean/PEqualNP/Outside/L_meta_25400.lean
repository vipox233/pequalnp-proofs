import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25400 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409149 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [8]⟩, ⟨.not, [9]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [10, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
