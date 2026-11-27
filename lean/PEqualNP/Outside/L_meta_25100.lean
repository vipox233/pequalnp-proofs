import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25100 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274845501 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.not, [5]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
