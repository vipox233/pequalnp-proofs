import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23159

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [10, 6]⟩,
      ⟨GateOp.and, [11, 9]⟩,
      ⟨GateOp.or, [12, 2]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.or, [14, 8]⟩,
      ⟨GateOp.or, [11, 9]⟩,
      ⟨GateOp.and, [16, 15]⟩,
      ⟨GateOp.or, [17, 3]⟩
    ],
    output := 18 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (64765 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_23159

theorem PEqualNP.Outside.L_meta_23159 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (64765 : ℕ).testBit (6 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_23159.ckt, PEqualNP.Outside.L_meta_23159.mono, by decide, PEqualNP.Outside.L_meta_23159.rep⟩
