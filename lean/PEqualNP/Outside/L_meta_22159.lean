import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22159

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 3]⟩,
      ⟨GateOp.and, [11, 5]⟩,
      ⟨GateOp.or, [12, 4]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.or, [16, 13]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.or, [18, 9]⟩,
      ⟨GateOp.and, [19, 0]⟩,
      ⟨GateOp.or, [20, 17]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840695 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22159

theorem PEqualNP.Outside.L_meta_22159 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840695 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22159.ckt, PEqualNP.Outside.L_meta_22159.mono, by decide, PEqualNP.Outside.L_meta_22159.rep⟩
