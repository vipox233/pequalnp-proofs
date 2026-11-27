import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22897

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [15, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [14, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 21] }], output := 22 }

end PEqualNP.Outside.L_meta_22897

theorem PEqualNP.Outside.L_meta_22897 :
PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940478 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  refine ⟨PEqualNP.Outside.L_meta_22897.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22897.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
