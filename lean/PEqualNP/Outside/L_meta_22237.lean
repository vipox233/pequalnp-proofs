import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22237 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
