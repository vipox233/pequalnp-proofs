import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23457 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2150333 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [8, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
