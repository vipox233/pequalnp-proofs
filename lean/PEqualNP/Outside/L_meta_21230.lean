import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21230_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [6, 1]⟩,
    ⟨GateOp.or, [7, 2]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [13, 11]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [15, 0]⟩,
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
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (515967 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21230_aux

theorem PEqualNP.Outside.L_meta_21230 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (515967 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21230_aux.C, PEqualNP.Outside.L_meta_21230_aux.C_ok, PEqualNP.Outside.L_meta_21230_aux.C_size, PEqualNP.Outside.L_meta_21230_aux.C_rep⟩
