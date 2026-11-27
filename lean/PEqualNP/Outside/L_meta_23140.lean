import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23140.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..2 are the left vertex, 3..8 the right vertex;
gate `j` writes wire `9 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [7, 13]⟩, ⟨GateOp.and, [11, 14]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_23140.Helpers

theorem PEqualNP.Outside.L_meta_23140 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (13174 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_23140.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23140.Helpers.witness]
