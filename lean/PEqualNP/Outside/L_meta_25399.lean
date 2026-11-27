import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25399 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409148 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.and, [6, 0]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 1]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [3, 2]⟩, ⟨.not, [5]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
