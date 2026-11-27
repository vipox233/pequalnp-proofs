import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24500 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147373 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [7]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
