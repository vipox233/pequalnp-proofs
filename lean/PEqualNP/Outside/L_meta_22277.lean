import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22277.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.not, [16]⟩, ⟨GateOp.or, [12, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22277.Helpers

theorem PEqualNP.Outside.L_meta_22277 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22277.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22277.Helpers.witness]
