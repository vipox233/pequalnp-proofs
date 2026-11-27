import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_23401 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (118588 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
