import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22506

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [6, 1]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.and, [11, 13]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [4, 12]⟩,
      ⟨GateOp.and, [17, 16]⟩,
      ⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.and, [19, 7]⟩,
      ⟨GateOp.or, [18, 15]⟩,
      ⟨GateOp.or, [21, 20]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1898228 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22506

theorem PEqualNP.Outside.L_meta_22506 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898228 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22506.ckt, PEqualNP.Outside.L_meta_22506.mono, by decide, PEqualNP.Outside.L_meta_22506.rep⟩
