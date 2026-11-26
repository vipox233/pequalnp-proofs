import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22225

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [11, 0]⟩,
      ⟨GateOp.or, [1, 10]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.or, [3, 14]⟩,
      ⟨GateOp.or, [14, 8]⟩,
      ⟨GateOp.and, [13, 16]⟩,
      ⟨GateOp.or, [15, 14]⟩,
      ⟨GateOp.or, [18, 12]⟩,
      ⟨GateOp.and, [19, 20]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (849715 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22225

theorem PEqualNP.Outside.L_meta_22225 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849715 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22225.ckt, PEqualNP.Outside.L_meta_22225.mono, by decide, PEqualNP.Outside.L_meta_22225.rep⟩
