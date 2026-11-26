import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21341

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [8, 0]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [10, 0]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [13, 3]⟩,
      ⟨GateOp.and, [14, 15]⟩,
      ⟨GateOp.and, [11, 10]⟩,
      ⟨GateOp.or, [17, 16]⟩,
      ⟨GateOp.or, [9, 18]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (112092 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21341

theorem PEqualNP.Outside.L_meta_21341 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112092 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21341.ckt, PEqualNP.Outside.L_meta_21341.mono, by decide, PEqualNP.Outside.L_meta_21341.rep⟩
