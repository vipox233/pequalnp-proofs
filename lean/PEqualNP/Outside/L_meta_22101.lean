import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22101 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17214 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [15, 14]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
