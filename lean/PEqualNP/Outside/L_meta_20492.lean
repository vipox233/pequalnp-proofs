import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20492

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [5, 9]⟩,
      ⟨GateOp.or, [6, 10]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.and, [1, 11]⟩,
      ⟨GateOp.and, [8, 12]⟩,
      ⟨GateOp.or, [13, 14]⟩
    ],
    output := 15 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (1494 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_20492

theorem PEqualNP.Outside.L_meta_20492 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (1494 : ℕ).testBit (5 * u.val + v.val)) 8 :=
  ⟨PEqualNP.Outside.L_meta_20492.ckt, PEqualNP.Outside.L_meta_20492.mono, by decide, PEqualNP.Outside.L_meta_20492.rep⟩
