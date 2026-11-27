import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25196 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18365 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [7, 14]⟩], 15⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
