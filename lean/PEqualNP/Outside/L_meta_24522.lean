import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24522 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180527 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.not, [4]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [5, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [8, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
