import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22514.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..3 are the left vertex, 4..9 the right vertex;
gate `j` writes wire `10 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [0, 16]⟩, ⟨GateOp.or, [5, 18]⟩, ⟨GateOp.or, [13, 19]⟩, ⟨GateOp.and, [17, 20]⟩, ⟨GateOp.or, [4, 21]⟩], 22⟩

end PEqualNP.Outside.L_meta_22514.Helpers

theorem PEqualNP.Outside.L_meta_22514 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899769 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  unfold PEqualNP.Represents.RepSizeAtMost
  refine ⟨PEqualNP.Outside.L_meta_22514.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22514.Helpers.witness]
