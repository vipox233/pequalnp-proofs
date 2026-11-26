import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21345_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 4]⟩], 19⟩

lemma h_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 11 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (112379 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_21345_aux

theorem PEqualNP.Outside.L_meta_21345 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112379 : ℕ).testBit (5 * u.val + v.val)) 11)  := by
  exact ⟨PEqualNP.Outside.L_meta_21345_aux.circ, PEqualNP.Outside.L_meta_21345_aux.h_mono, PEqualNP.Outside.L_meta_21345_aux.h_sz, PEqualNP.Outside.L_meta_21345_aux.h_rep⟩
