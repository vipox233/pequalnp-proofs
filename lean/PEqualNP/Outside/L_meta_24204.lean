import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24204 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582673 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.not, [10]⟩], 11⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
