import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21512_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩], 9⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 5 := by decide +kernel

end PEqualNP.Outside.L_meta_21512_aux

theorem PEqualNP.Outside.L_meta_21512 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (471 : ℕ).testBit (5 * min i.val j.val + max i.val j.val))  := by
  exact ⟨PEqualNP.Outside.L_meta_21512_aux.circ, PEqualNP.Outside.L_meta_21512_aux.h_ok, PEqualNP.Outside.L_meta_21512_aux.h_sz, by decide +kernel⟩
