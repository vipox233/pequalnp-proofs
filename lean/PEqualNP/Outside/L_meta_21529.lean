import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21529 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17052637 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [8]⟩], 9⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
