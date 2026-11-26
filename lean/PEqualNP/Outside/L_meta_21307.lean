import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21307

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [4, 6]⟩,
      ⟨GateOp.or, [0, 11]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [13, 5]⟩,
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.and, [12, 16]⟩,
      ⟨GateOp.and, [9, 10]⟩,
      ⟨GateOp.or, [17, 18]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (103674 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21307

theorem PEqualNP.Outside.L_meta_21307 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103674 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21307.ckt, PEqualNP.Outside.L_meta_21307.mono, by decide, PEqualNP.Outside.L_meta_21307.rep⟩
