import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25290 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149436 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 12]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
