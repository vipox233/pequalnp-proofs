import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22019 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33553 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
