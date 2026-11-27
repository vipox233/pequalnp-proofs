import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24158 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266326 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [7, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
