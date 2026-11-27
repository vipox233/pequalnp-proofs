import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24321 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4377519 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [7, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
