import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24988 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (12783549 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.not, [7]⟩, ⟨.and, [12, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
