import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22602.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [0, 17]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [4, 19]⟩, ⟨GateOp.and, [20, 21]⟩], 22⟩

end PEqualNP.Outside.L_meta_22602.Helpers

theorem PEqualNP.Outside.L_meta_22602 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (2072186 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22602.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22602.Helpers.witness]
