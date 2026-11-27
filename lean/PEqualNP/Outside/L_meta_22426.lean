import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22426.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [4, 5]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [0, 15]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22426.Helpers

theorem PEqualNP.Outside.L_meta_22426 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17336 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22426.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22426.Helpers.witness]
