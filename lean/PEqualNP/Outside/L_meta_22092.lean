import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_22092 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17079 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let C : Circuit := ⟨[⟨.not, [1]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 8]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 10]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [14, 12]⟩, ⟨.not, [15]⟩], 16⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
