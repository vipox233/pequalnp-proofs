import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22409

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [4, 11]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [0, 13]⟩,
      ⟨GateOp.and, [1, 14]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.and, [3, 15]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [20, 18]⟩,
      ⟨GateOp.or, [21, 19]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (907197 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22409

theorem PEqualNP.Outside.L_meta_22409 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907197 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22409.ckt, PEqualNP.Outside.L_meta_22409.mono, by decide, PEqualNP.Outside.L_meta_22409.rep⟩
