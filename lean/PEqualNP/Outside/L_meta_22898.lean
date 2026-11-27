import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22898.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [9, 17]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.and, [0, 18]⟩, ⟨GateOp.and, [11, 20]⟩, ⟨GateOp.or, [19, 22]⟩, ⟨GateOp.or, [21, 23]⟩], 24⟩

end PEqualNP.Outside.L_meta_22898.Helpers

theorem PEqualNP.Outside.L_meta_22898 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947512 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22898.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22898.Helpers.witness]
