import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21128_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [10, 9]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [13, 4]⟩,
    ⟨GateOp.or, [14, 5]⟩,
    ⟨GateOp.or, [2, 11]⟩,
    ⟨GateOp.or, [12, 16]⟩,
    ⟨GateOp.and, [15, 17]⟩
    ]
    output := 18 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 10 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (36253 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21128_aux

theorem PEqualNP.Outside.L_meta_21128 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36253 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21128_aux.C, PEqualNP.Outside.L_meta_21128_aux.C_ok, PEqualNP.Outside.L_meta_21128_aux.C_size, PEqualNP.Outside.L_meta_21128_aux.C_rep⟩
