import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25359 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197423 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.not, [5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [11]⟩, ⟨.or, [4, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
