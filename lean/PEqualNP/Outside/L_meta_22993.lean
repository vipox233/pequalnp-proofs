import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22993

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [0, 8]⟩,
    ⟨.or, [4, 6]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact ⟨by first | exact Or.inl rfl | exact Or.inr rfl, by decide⟩

end PEqualNP.Outside.L_meta_22993

open PEqualNP.Outside.L_meta_22993 in
set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_meta_22993 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1838 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
