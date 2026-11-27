import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24993 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549151 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
