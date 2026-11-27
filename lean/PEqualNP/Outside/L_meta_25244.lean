import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25244 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50619 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
