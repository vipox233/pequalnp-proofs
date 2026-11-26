import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21290

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [4, 9]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.and, [0, 11]⟩,
      ⟨GateOp.and, [1, 12]⟩,
      ⟨GateOp.and, [2, 10]⟩,
      ⟨GateOp.and, [3, 4]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [17, 15]⟩,
      ⟨GateOp.or, [18, 16]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (40407 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21290

theorem PEqualNP.Outside.L_meta_21290 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40407 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21290.ckt, PEqualNP.Outside.L_meta_21290.mono, by decide, PEqualNP.Outside.L_meta_21290.rep⟩
