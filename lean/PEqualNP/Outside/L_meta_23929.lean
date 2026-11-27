import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23929 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4362 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
