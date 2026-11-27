import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21677 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275161 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [11, 10]⟩, ⟨.not, [12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
