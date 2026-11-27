import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22392

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [6, 10]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [11, 8]⟩,
      ⟨GateOp.or, [1, 0]⟩,
      ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [16, 14]⟩,
      ⟨GateOp.and, [17, 19]⟩,
      ⟨GateOp.and, [12, 18]⟩,
      ⟨GateOp.or, [20, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (849716 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22392

theorem PEqualNP.Outside.L_meta_22392 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849716 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22392.ckt, PEqualNP.Outside.L_meta_22392.mono, by decide, PEqualNP.Outside.L_meta_22392.rep⟩
