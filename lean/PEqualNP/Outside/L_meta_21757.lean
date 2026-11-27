import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21757 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807511 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [10, 3]⟩, ⟨.not, [11]⟩, ⟨.and, [4, 12]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [14, 13]⟩, ⟨.not, [15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
