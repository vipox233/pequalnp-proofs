import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25209 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33965 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [10, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
