import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23147

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }], output := 18 }

end PEqualNP.Outside.L_meta_23147

theorem PEqualNP.Outside.L_meta_23147 :
PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (16254 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  refine ⟨PEqualNP.Outside.L_meta_23147.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23147.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
