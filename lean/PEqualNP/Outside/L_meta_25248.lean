import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25248 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50718 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
