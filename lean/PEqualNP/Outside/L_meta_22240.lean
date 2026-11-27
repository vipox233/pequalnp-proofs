import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22240 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18232 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
