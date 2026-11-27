import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22312.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [6, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [9, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22312.Helpers

theorem PEqualNP.Outside.L_meta_22312 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17947 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22312.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22312.Helpers.witness]
