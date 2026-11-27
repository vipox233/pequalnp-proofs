import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22130_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [16, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [12, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [17, 18]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 20]⟩], 21⟩

lemma h_ok : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 12 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (838773 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22130_aux

theorem PEqualNP.Outside.L_meta_22130 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838773 : ℕ).testBit (6 * u.val + v.val)) 12)  := by
  exact ⟨PEqualNP.Outside.L_meta_22130_aux.circ, PEqualNP.Outside.L_meta_22130_aux.h_ok, PEqualNP.Outside.L_meta_22130_aux.h_sz, PEqualNP.Outside.L_meta_22130_aux.h_rep⟩
