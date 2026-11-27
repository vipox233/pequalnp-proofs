import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24028 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17043659 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
