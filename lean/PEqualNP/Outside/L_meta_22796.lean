import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22796.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [6, 15]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [10, 16]⟩, ⟨GateOp.and, [6, 17]⟩, ⟨GateOp.or, [4, 18]⟩, ⟨GateOp.and, [2, 19]⟩, ⟨GateOp.or, [0, 20]⟩, ⟨GateOp.and, [17, 22]⟩, ⟨GateOp.or, [21, 23]⟩], 24⟩

end PEqualNP.Outside.L_meta_22796.Helpers

theorem PEqualNP.Outside.L_meta_22796 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (817022 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22796.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22796.Helpers.witness]
