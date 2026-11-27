import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22200 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17306 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [10, 5]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 14]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
