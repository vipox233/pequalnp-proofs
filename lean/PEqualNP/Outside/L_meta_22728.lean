import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22728.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [9, 16]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [10, 18]⟩, ⟨GateOp.or, [11, 19]⟩, ⟨GateOp.or, [14, 20]⟩, ⟨GateOp.and, [21, 22]⟩], 23⟩

end PEqualNP.Outside.L_meta_22728.Helpers

theorem PEqualNP.Outside.L_meta_22728 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883445 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22728.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22728.Helpers.witness]
