import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22187

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.or, [8, 6]⟩,
      ⟨GateOp.or, [5, 1]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [3, 13]⟩,
      ⟨GateOp.or, [14, 12]⟩,
      ⟨GateOp.and, [16, 17]⟩,
      ⟨GateOp.or, [10, 9]⟩,
      ⟨GateOp.and, [19, 15]⟩,
      ⟨GateOp.or, [18, 20]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841588 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22187

theorem PEqualNP.Outside.L_meta_22187 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841588 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22187.ckt, PEqualNP.Outside.L_meta_22187.mono, by decide, PEqualNP.Outside.L_meta_22187.rep⟩
