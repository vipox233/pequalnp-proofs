import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22404_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [3, 0]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [11, 9]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.and, [2, 14]⟩,
    ⟨GateOp.and, [5, 10]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.and, [12, 13]⟩,
    ⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.or, [17, 18]⟩,
    ⟨GateOp.and, [19, 4]⟩,
    ⟨GateOp.or, [20, 21]⟩
    ]
    output := 22 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 13 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (904046 : ℕ).testBit (6 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_22404_aux

theorem PEqualNP.Outside.L_meta_22404 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904046 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22404_aux.C, PEqualNP.Outside.L_meta_22404_aux.C_ok, PEqualNP.Outside.L_meta_22404_aux.C_size, PEqualNP.Outside.L_meta_22404_aux.C_rep⟩
