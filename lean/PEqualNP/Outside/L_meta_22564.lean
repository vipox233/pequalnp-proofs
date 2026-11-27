import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22564

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  { gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [19, 20] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 21] }], output := 22 }

end PEqualNP.Outside.L_meta_22564

theorem PEqualNP.Outside.L_meta_22564 :
PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948539 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨PEqualNP.Outside.L_meta_22564.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22564.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
