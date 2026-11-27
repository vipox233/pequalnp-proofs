import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22777_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [18, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 21]⟩], 22⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 14 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1965694 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22777_aux

theorem PEqualNP.Outside.L_meta_22777 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965694 : ℕ).testBit (6 * u.val + v.val)) 14)  := by
  exact ⟨PEqualNP.Outside.L_meta_22777_aux.circ, PEqualNP.Outside.L_meta_22777_aux.h_ok, PEqualNP.Outside.L_meta_22777_aux.h_sz, PEqualNP.Outside.L_meta_22777_aux.h_rep⟩
