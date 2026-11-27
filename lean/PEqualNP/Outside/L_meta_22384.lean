import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22384

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.and, [16, 12]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [4, 14]⟩,
      ⟨GateOp.and, [18, 19]⟩,
      ⟨GateOp.and, [9, 2]⟩,
      ⟨GateOp.or, [20, 17]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843062 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22384

theorem PEqualNP.Outside.L_meta_22384 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843062 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22384.ckt, PEqualNP.Outside.L_meta_22384.mono, by decide, PEqualNP.Outside.L_meta_22384.rep⟩
