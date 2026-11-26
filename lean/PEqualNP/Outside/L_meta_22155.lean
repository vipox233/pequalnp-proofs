import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22155

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.or, [4, 1]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [10, 3]⟩,
      ⟨GateOp.or, [0, 13]⟩,
      ⟨GateOp.and, [0, 11]⟩,
      ⟨GateOp.and, [14, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩,
      ⟨GateOp.or, [17, 12]⟩,
      ⟨GateOp.and, [18, 19]⟩,
      ⟨GateOp.or, [16, 20]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840625 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22155

theorem PEqualNP.Outside.L_meta_22155 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840625 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22155.ckt, PEqualNP.Outside.L_meta_22155.mono, by decide, PEqualNP.Outside.L_meta_22155.rep⟩
