import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22669_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 20]⟩], 22⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841649 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22669_aux

theorem PEqualNP.Outside.L_meta_22669 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841649 : ℕ).testBit (6 * u.val + v.val)) 14)  := by
  exact ⟨PEqualNP.Outside.L_meta_22669_aux.circ, PEqualNP.Outside.L_meta_22669_aux.h_ok, PEqualNP.Outside.L_meta_22669_aux.h_sz, PEqualNP.Outside.L_meta_22669_aux.h_rep⟩
