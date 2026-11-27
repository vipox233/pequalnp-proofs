import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24985 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6524735 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
