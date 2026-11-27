import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24829 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149565 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
