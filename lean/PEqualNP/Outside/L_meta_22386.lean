import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22386

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [7, 1]⟩,
      ⟨GateOp.or, [4, 10]⟩,
      ⟨GateOp.or, [6, 0]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.and, [12, 11]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [15, 9]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [16, 18]⟩,
      ⟨GateOp.and, [3, 19]⟩,
      ⟨GateOp.or, [20, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843065 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22386

theorem PEqualNP.Outside.L_meta_22386 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843065 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22386.ckt, PEqualNP.Outside.L_meta_22386.mono, by decide, PEqualNP.Outside.L_meta_22386.rep⟩
