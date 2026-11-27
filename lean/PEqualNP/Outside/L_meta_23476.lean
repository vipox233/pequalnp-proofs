import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23476 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (440 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
