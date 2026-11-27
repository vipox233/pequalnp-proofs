import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24669 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
