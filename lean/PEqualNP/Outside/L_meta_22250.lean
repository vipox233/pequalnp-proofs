import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22250_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [5, 1]⟩,
    ⟨GateOp.or, [3, 10]⟩,
    ⟨GateOp.or, [9, 1]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.or, [13, 2]⟩,
    ⟨GateOp.or, [8, 14]⟩,
    ⟨GateOp.and, [16, 15]⟩,
    ⟨GateOp.and, [17, 11]⟩,
    ⟨GateOp.and, [2, 6]⟩,
    ⟨GateOp.or, [19, 20]⟩,
    ⟨GateOp.or, [21, 18]⟩
    ]
    output := 22 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 13 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (815996 : ℕ).testBit (6 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_22250_aux

theorem PEqualNP.Outside.L_meta_22250 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815996 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22250_aux.C, PEqualNP.Outside.L_meta_22250_aux.C_ok, PEqualNP.Outside.L_meta_22250_aux.C_size, PEqualNP.Outside.L_meta_22250_aux.C_rep⟩
