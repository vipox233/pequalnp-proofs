import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22204.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [11, 18]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.or, [4, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_22204.Helpers

theorem PEqualNP.Outside.L_meta_22204 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843259 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22204.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22204.Helpers.witness]
