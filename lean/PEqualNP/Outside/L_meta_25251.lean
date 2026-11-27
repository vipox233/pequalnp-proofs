import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25251 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50733 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
