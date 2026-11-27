import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24193 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2113929 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
