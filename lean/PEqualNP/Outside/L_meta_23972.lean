import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23972_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 11]⟩], 12⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 8 := by decide +kernel

end PEqualNP.Outside.L_meta_23972_aux

theorem PEqualNP.Outside.L_meta_23972 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8797 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23972_aux.circ, PEqualNP.Outside.L_meta_23972_aux.h_ok, PEqualNP.Outside.L_meta_23972_aux.h_sz, by decide +kernel⟩
