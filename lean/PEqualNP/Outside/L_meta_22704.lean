import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22704.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.and, [10, 15]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [4, 17]⟩, ⟨GateOp.or, [1, 18]⟩, ⟨GateOp.and, [20, 21]⟩, ⟨GateOp.or, [19, 22]⟩], 23⟩

end PEqualNP.Outside.L_meta_22704.Helpers

theorem PEqualNP.Outside.L_meta_22704 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903149 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22704.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22704.Helpers.witness]
