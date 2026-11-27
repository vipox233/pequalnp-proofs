import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23148_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 17]⟩], 18⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 10 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 3) (v : Fin 6) => (29436 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_23148_aux

theorem PEqualNP.Outside.L_meta_23148 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (29436 : ℕ).testBit (6 * u.val + v.val)) 10)  := by
  exact ⟨PEqualNP.Outside.L_meta_23148_aux.circ, PEqualNP.Outside.L_meta_23148_aux.h_ok, PEqualNP.Outside.L_meta_23148_aux.h_sz, PEqualNP.Outside.L_meta_23148_aux.h_rep⟩
