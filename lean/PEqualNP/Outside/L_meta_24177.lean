import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24177 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266836 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [2, 5]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 12]⟩, ⟨.not, [13]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [11, 15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
