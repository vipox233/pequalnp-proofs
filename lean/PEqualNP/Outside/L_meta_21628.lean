import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21628

open PEqualNP.CircuitLowerBounds

-- Inputs occupy wires 0 through 4. The last gate combines the pair {1, 3}
-- with the accepted inputs containing 0 or 2.
private def witness : Circuit :=
  ⟨[⟨.and, [1, 3]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩,
    ⟨.or, [0, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.not, [9]⟩,
    ⟨.and, [6, 10]⟩, ⟨.or, [5, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_21628

theorem PEqualNP.Outside.L_meta_21628 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4507 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21628.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_21628.witness] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel