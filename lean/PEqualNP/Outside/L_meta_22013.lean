import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22013 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18220 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
