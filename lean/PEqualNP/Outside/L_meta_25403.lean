import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25403 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6410046 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
