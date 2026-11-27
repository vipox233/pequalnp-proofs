import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22941_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.and, [2, 14]⟩, ⟨GateOp.and, [3, 16]⟩, ⟨GateOp.or, [17, 20]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.or, [19, 22]⟩], 23⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem represents : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (1949308 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22941_aux

theorem PEqualNP.Outside.L_meta_22941 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1949308 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  exact ⟨PEqualNP.Outside.L_meta_22941_aux.circ, PEqualNP.Outside.L_meta_22941_aux.shape, by decide, PEqualNP.Outside.L_meta_22941_aux.represents⟩
