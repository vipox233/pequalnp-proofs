import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22689_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [7, 1]⟩,
    ⟨GateOp.or, [3, 6]⟩,
    ⟨GateOp.or, [9, 13]⟩,
    ⟨GateOp.or, [8, 2]⟩,
    ⟨GateOp.or, [4, 10]⟩,
    ⟨GateOp.or, [0, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.and, [16, 19]⟩,
    ⟨GateOp.and, [17, 18]⟩,
    ⟨GateOp.or, [13, 4]⟩,
    ⟨GateOp.or, [20, 21]⟩
    ]
    output := 23 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 14 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843196 : ℕ).testBit (6 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_22689_aux

theorem PEqualNP.Outside.L_meta_22689 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843196 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨PEqualNP.Outside.L_meta_22689_aux.C, PEqualNP.Outside.L_meta_22689_aux.C_ok, PEqualNP.Outside.L_meta_22689_aux.C_size, PEqualNP.Outside.L_meta_22689_aux.C_rep⟩
