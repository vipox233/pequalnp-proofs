import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24136 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [6]⟩,
    ⟨.or, [3, 7]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [2, 3]⟩,
    ⟨.or, [5, 10]⟩, ⟨.not, [9]⟩, ⟨.and, [11, 12]⟩], 13⟩,
    ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
