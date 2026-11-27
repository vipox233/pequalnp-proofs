import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22109 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17964 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
