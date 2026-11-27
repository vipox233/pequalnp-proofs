import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21483 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (143 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [4]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
