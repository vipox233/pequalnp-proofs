import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24143_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [10, 13]⟩], 14⟩

theorem witness_fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem solve : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283225 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, witness_fan, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_24143_aux

theorem PEqualNP.Outside.L_meta_24143 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283225 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_24143_aux.solve
