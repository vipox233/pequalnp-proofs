import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22513.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [3, 17]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.and, [14, 19]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.and, [19, 21]⟩], 22⟩

end PEqualNP.Outside.L_meta_22513.Helpers

theorem PEqualNP.Outside.L_meta_22513 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899768 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22513.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22513.Helpers.witness]
