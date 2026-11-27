import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25247 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50717 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [4]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [9]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
