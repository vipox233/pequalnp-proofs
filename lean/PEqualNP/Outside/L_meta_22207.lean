import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22207

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [15, 7]⟩,
      ⟨GateOp.or, [16, 14]⟩,
      ⟨GateOp.and, [17, 11]⟩,
      ⟨GateOp.or, [16, 0]⟩,
      ⟨GateOp.and, [19, 12]⟩,
      ⟨GateOp.or, [20, 18]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843582 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22207

theorem PEqualNP.Outside.L_meta_22207 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843582 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22207.ckt, PEqualNP.Outside.L_meta_22207.mono, by decide, PEqualNP.Outside.L_meta_22207.rep⟩
