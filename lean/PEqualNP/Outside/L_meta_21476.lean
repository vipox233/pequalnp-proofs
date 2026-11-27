import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21476 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25502 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩,
      ⟨.and, [6, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 5]⟩,
      ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp
