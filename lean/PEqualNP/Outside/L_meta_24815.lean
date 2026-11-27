import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24815 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147773 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.not, [1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [4, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
