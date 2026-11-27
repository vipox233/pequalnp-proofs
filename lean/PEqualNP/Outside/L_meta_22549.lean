import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22549

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 2]⟩,
      ⟨GateOp.and, [2, 5]⟩,
      ⟨GateOp.or, [12, 1]⟩,
      ⟨GateOp.or, [13, 3]⟩,
      ⟨GateOp.or, [14, 9]⟩,
      ⟨GateOp.or, [5, 0]⟩,
      ⟨GateOp.or, [16, 6]⟩,
      ⟨GateOp.and, [17, 15]⟩,
      ⟨GateOp.or, [18, 4]⟩,
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.and, [20, 11]⟩,
      ⟨GateOp.or, [21, 19]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1947641 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22549

theorem PEqualNP.Outside.L_meta_22549 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947641 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22549.ckt, PEqualNP.Outside.L_meta_22549.mono, by decide, PEqualNP.Outside.L_meta_22549.rep⟩
