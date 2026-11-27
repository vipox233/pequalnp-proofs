import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22876.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.or, [7, 16]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [3, 18]⟩, ⟨GateOp.and, [12, 19]⟩, ⟨GateOp.or, [12, 19]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.or, [9, 21]⟩, ⟨GateOp.and, [22, 23]⟩], 24⟩

end PEqualNP.Outside.L_meta_22876.Helpers

theorem PEqualNP.Outside.L_meta_22876 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883965 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22876.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22876.Helpers.witness]
