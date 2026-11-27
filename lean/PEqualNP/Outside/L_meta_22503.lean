import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22503_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[
  ⟨GateOp.or, [5, 1]⟩,
  ⟨GateOp.or, [2, 3]⟩,
  ⟨GateOp.or, [6, 10]⟩,
  ⟨GateOp.or, [4, 0]⟩,
  ⟨GateOp.or, [8, 11]⟩,
  ⟨GateOp.or, [10, 14]⟩,
  ⟨GateOp.and, [7, 2]⟩,
  ⟨GateOp.or, [7, 14]⟩,
  ⟨GateOp.or, [15, 9]⟩,
  ⟨GateOp.and, [17, 12]⟩,
  ⟨GateOp.and, [18, 13]⟩,
  ⟨GateOp.or, [19, 20]⟩,
  ⟨GateOp.or, [21, 16]⟩
], 22⟩

lemma h_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 13 := by decide +kernel

lemma h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1898098 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22503_aux

theorem PEqualNP.Outside.L_meta_22503 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898098 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22503_aux.circ, PEqualNP.Outside.L_meta_22503_aux.h_mono, PEqualNP.Outside.L_meta_22503_aux.h_sz, PEqualNP.Outside.L_meta_22503_aux.h_rep⟩
