import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22613_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩], 22⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (292795 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22613_aux

theorem PEqualNP.Outside.L_meta_22613 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292795 : ℕ).testBit (6 * u.val + v.val)) 14)  := by
  exact ⟨PEqualNP.Outside.L_meta_22613_aux.circ, PEqualNP.Outside.L_meta_22613_aux.h_ok, PEqualNP.Outside.L_meta_22613_aux.h_sz, PEqualNP.Outside.L_meta_22613_aux.h_rep⟩
