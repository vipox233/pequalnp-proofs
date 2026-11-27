import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21553 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8799 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [9, 8]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
