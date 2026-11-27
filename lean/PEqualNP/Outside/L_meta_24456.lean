import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24456 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101051 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.not, [2]⟩, ⟨.not, [4]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
