import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23666_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit :=
  ⟨[⟨.or, [3, 0]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [9, 1]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [7, 11]⟩,
    ⟨.or, [12, 8]⟩], 13⟩

theorem h_fit : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem h_sz : circ.size ≤ 8 := by
  decide +kernel

theorem h_eval : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36029 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23666_aux

theorem PEqualNP.Outside.L_meta_23666 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (36029 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23666_aux.circ, PEqualNP.Outside.L_meta_23666_aux.h_fit, PEqualNP.Outside.L_meta_23666_aux.h_sz, PEqualNP.Outside.L_meta_23666_aux.h_eval⟩
