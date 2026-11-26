import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19714
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [4, 15]⟩, ⟨GateOp.or, [6, 15]⟩, ⟨GateOp.or, [5, 16]⟩, ⟨GateOp.or, [3, 17]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.or, [6, 19]⟩, ⟨GateOp.or, [4, 20]⟩, ⟨GateOp.or, [9, 21]⟩, ⟨GateOp.or, [20, 21]⟩, ⟨GateOp.or, [18, 22]⟩, ⟨GateOp.or, [2, 23]⟩, ⟨GateOp.or, [0, 24]⟩, ⟨GateOp.or, [3, 25]⟩, ⟨GateOp.or, [1, 26]⟩, ⟨GateOp.or, [5, 27]⟩, ⟨GateOp.or, [8, 28]⟩, ⟨GateOp.or, [14, 30]⟩, ⟨GateOp.or, [11, 31]⟩, ⟨GateOp.or, [13, 31]⟩, ⟨GateOp.or, [13, 34]⟩, ⟨GateOp.or, [11, 35]⟩, ⟨GateOp.or, [8, 38]⟩, ⟨GateOp.and, [1, 25]⟩, ⟨GateOp.and, [29, 40]⟩, ⟨GateOp.and, [32, 37]⟩, ⟨GateOp.and, [33, 41]⟩, ⟨GateOp.and, [36, 39]⟩, ⟨GateOp.or, [42, 43]⟩, ⟨GateOp.or, [47, 44]⟩, ⟨GateOp.or, [48, 45]⟩, ⟨GateOp.or, [49, 46]⟩], 50⟩

theorem shape : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem right : Represents (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_19714

theorem PEqualNP.Outside.L_meta_19714 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 35 := by
  exact ⟨PEqualNP.Outside.L_meta_19714.circ, PEqualNP.Outside.L_meta_19714.shape, by decide, PEqualNP.Outside.L_meta_19714.right⟩
