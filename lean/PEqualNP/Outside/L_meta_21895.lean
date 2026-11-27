import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21895 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33824 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [0, 5]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [8, 9]⟩
  ], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
