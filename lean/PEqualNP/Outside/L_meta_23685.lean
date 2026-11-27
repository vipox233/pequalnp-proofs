import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23685

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [3, 12]⟩,
      ⟨GateOp.or, [14, 8]⟩,
      ⟨GateOp.and, [15, 11]⟩,
      ⟨GateOp.and, [13, 10]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 4]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816745 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_23685

theorem PEqualNP.Outside.L_meta_23685 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816745 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_23685.ckt, PEqualNP.Outside.L_meta_23685.mono, by decide, PEqualNP.Outside.L_meta_23685.rep⟩
