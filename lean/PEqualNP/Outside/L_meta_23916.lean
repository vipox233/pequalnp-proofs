import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23916 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807639 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [7, 10]⟩], 11⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
