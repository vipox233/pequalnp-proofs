import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_25256 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50843 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [5, 12]⟩, ⟨.not, [13]⟩, ⟨.and, [11, 14]⟩], 15⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
