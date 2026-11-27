import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22430_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [18]⟩], 19⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

end PEqualNP.Outside.L_meta_22430_aux

theorem PEqualNP.Outside.L_meta_22430 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18073 : ℕ).testBit (6 * min i.val j.val + max i.val j.val))  := by
  exact ⟨PEqualNP.Outside.L_meta_22430_aux.circ, PEqualNP.Outside.L_meta_22430_aux.h_ok, PEqualNP.Outside.L_meta_22430_aux.h_sz, by decide +kernel⟩
