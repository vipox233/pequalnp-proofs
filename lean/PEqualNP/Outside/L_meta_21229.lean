import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21229_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [7, 1]⟩,
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.and, [10, 9]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.or, [12, 8]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [11, 15]⟩,
    ⟨GateOp.or, [16, 4]⟩,
    ⟨GateOp.or, [17, 5]⟩
    ]
    output := 18 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 10 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (507643 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21229_aux

theorem PEqualNP.Outside.L_meta_21229 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (507643 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21229_aux.C, PEqualNP.Outside.L_meta_21229_aux.C_ok, PEqualNP.Outside.L_meta_21229_aux.C_size, PEqualNP.Outside.L_meta_21229_aux.C_rep⟩
