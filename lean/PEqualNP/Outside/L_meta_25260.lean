import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25260 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50863 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 5]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [4]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
