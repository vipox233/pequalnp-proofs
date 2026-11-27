import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24082 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283227 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [6, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [7, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
