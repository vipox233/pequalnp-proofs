import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_24726 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52670 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[
    ⟨.not, [3]⟩,
    ⟨.and, [1, 6]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [7, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
