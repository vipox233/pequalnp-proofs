import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25387 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6376383 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [0, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
