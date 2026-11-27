import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22305.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.and, [10, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22305.Helpers

theorem PEqualNP.Outside.L_meta_22305 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17083 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22305.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22305.Helpers.witness]
