import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22016 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18351 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.not, [4]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [5]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
