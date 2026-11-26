import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21225

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [7, 1]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [3, 13]⟩,
      ⟨GateOp.and, [14, 9]⟩,
      ⟨GateOp.and, [12, 10]⟩,
      ⟨GateOp.or, [15, 11]⟩,
      ⟨GateOp.or, [17, 16]⟩
    ],
    output := 18 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (245499 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21225

theorem PEqualNP.Outside.L_meta_21225 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (245499 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21225.ckt, PEqualNP.Outside.L_meta_21225.mono, by decide, PEqualNP.Outside.L_meta_21225.rep⟩
