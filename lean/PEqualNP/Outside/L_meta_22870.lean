import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22870.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 15-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.and, [4, 15]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [0, 16]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.and, [11, 20]⟩, ⟨GateOp.or, [21, 22]⟩, ⟨GateOp.or, [17, 23]⟩], 24⟩

end PEqualNP.Outside.L_meta_22870.Helpers

theorem PEqualNP.Outside.L_meta_22870 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881980 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22870.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22870.Helpers.witness]
