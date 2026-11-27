import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22431_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 17]⟩], 19⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

end PEqualNP.Outside.L_meta_22431_aux

theorem PEqualNP.Outside.L_meta_22431 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18093 : ℕ).testBit (6 * min i.val j.val + max i.val j.val))  := by
  exact ⟨PEqualNP.Outside.L_meta_22431_aux.circ, PEqualNP.Outside.L_meta_22431_aux.h_ok, PEqualNP.Outside.L_meta_22431_aux.h_sz, by decide +kernel⟩
