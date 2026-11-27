import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22798

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [5, 7]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.or, [4, 6]⟩,
      ⟨GateOp.or, [7, 16]⟩,
      ⟨GateOp.and, [0, 13]⟩,
      ⟨GateOp.and, [1, 15]⟩,
      ⟨GateOp.and, [2, 17]⟩,
      ⟨GateOp.and, [3, 10]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.or, [22, 20]⟩,
      ⟨GateOp.or, [23, 21]⟩
    ],
    output := 24 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841655 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22798

theorem PEqualNP.Outside.L_meta_22798 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841655 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨PEqualNP.Outside.L_meta_22798.ckt, PEqualNP.Outside.L_meta_22798.mono, by decide, PEqualNP.Outside.L_meta_22798.rep⟩
