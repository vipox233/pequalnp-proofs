import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22394

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.or, [3, 2]⟩,
      ⟨GateOp.or, [10, 9]⟩,
      ⟨GateOp.and, [1, 8]⟩,
      ⟨GateOp.and, [11, 5]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.or, [4, 15]⟩,
      ⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.and, [18, 17]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [20, 19]⟩,
      ⟨GateOp.or, [16, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (849781 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22394

theorem PEqualNP.Outside.L_meta_22394 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849781 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22394.ckt, PEqualNP.Outside.L_meta_22394.mono, by decide, PEqualNP.Outside.L_meta_22394.rep⟩
