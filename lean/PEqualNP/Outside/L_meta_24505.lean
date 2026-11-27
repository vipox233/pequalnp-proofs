import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24505 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147503 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [9, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
