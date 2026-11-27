import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24722 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17338 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [6, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
