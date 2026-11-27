import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21917 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34088 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [10, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
