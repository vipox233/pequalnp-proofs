import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24842 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165567 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
