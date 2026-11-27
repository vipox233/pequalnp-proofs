import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25432 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549123 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [11, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [13, 12]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
