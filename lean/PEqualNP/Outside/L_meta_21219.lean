import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21219

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.and, [11, 12]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.and, [10, 14]⟩,
      ⟨GateOp.or, [9, 15]⟩,
      ⟨GateOp.or, [13, 16]⟩
    ],
    output := 17 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (241087 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21219

theorem PEqualNP.Outside.L_meta_21219 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241087 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  ⟨PEqualNP.Outside.L_meta_21219.ckt, PEqualNP.Outside.L_meta_21219.mono, by decide, PEqualNP.Outside.L_meta_21219.rep⟩
