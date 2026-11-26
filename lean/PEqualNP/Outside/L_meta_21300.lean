import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21300

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [9, 3]⟩,
      ⟨GateOp.and, [10, 4]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.and, [14, 12]⟩,
      ⟨GateOp.or, [15, 11]⟩,
      ⟨GateOp.or, [13, 8]⟩,
      ⟨GateOp.and, [17, 0]⟩,
      ⟨GateOp.or, [18, 16]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (47607 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21300

theorem PEqualNP.Outside.L_meta_21300 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47607 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21300.ckt, PEqualNP.Outside.L_meta_21300.mono, by decide, PEqualNP.Outside.L_meta_21300.rep⟩
