import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23388 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (117439 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
