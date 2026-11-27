import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23143.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.and, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_23143.Helpers

theorem PEqualNP.Outside.L_meta_23143 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14127 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23143.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23143.Helpers.witness]
