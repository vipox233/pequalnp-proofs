import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22320 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18091 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.not, [1]⟩, ⟨.and, [4, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [10]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 14]⟩, ⟨.not, [17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
