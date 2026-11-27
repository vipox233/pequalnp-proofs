import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25221 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36028 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [6, 3]⟩, ⟨.not, [8]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [10, 1]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
