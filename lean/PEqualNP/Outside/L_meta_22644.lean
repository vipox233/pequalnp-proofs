import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22644.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [1, 15]⟩, ⟨GateOp.and, [10, 16]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.or, [5, 18]⟩, ⟨GateOp.and, [20, 21]⟩, ⟨GateOp.or, [19, 22]⟩], 23⟩

end PEqualNP.Outside.L_meta_22644.Helpers

theorem PEqualNP.Outside.L_meta_22644 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (817006 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22644.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22644.Helpers.witness]
