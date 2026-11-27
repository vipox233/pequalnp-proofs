import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22279.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.not, [16]⟩, ⟨GateOp.or, [15, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22279.Helpers

theorem PEqualNP.Outside.L_meta_22279 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16945 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22279.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22279.Helpers.witness]
