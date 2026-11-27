import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21561 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (29535 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [1, 5]⟩, ⟨.not, [1]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [9, 8]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
