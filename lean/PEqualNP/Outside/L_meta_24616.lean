import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24616 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270649256 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 3]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
