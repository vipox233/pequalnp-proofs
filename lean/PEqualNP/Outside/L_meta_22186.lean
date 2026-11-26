import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22186

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [10, 6]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.or, [13, 2]⟩,
      ⟨GateOp.or, [15, 9]⟩,
      ⟨GateOp.and, [16, 12]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.and, [18, 14]⟩,
      ⟨GateOp.or, [19, 17]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841586 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22186

theorem PEqualNP.Outside.L_meta_22186 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841586 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22186.ckt, PEqualNP.Outside.L_meta_22186.mono, by decide, PEqualNP.Outside.L_meta_22186.rep⟩
