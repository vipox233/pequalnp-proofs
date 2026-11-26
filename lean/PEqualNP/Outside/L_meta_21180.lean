import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21180
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : Represents (fun (u : Fin 4) (v : Fin 5) => (103765 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_21180

theorem PEqualNP.Outside.L_meta_21180 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103765 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21180.circ, PEqualNP.Outside.L_meta_21180.shape, by decide, PEqualNP.Outside.L_meta_21180.right⟩
