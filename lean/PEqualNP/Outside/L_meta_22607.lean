import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22607_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 14]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [20, 19]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 4]⟩], 22⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 13 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (4028921 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22607_aux

theorem PEqualNP.Outside.L_meta_22607 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4028921 : ℕ).testBit (6 * u.val + v.val)) 13)  := by
  exact ⟨PEqualNP.Outside.L_meta_22607_aux.circ, PEqualNP.Outside.L_meta_22607_aux.h_ok, PEqualNP.Outside.L_meta_22607_aux.h_sz, PEqualNP.Outside.L_meta_22607_aux.h_rep⟩
