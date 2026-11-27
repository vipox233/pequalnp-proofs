import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22464 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18104 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.or, [6, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.not, [13]⟩, ⟨.and, [2, 14]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [16, 5]⟩, ⟨.and, [0, 17]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [19, 18]⟩], 20⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
