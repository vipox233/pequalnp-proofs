import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23884 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12623 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 10]⟩], 11⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
