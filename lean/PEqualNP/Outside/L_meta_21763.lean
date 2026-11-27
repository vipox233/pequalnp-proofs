import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21763.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [11, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_21763.Helpers

theorem PEqualNP.Outside.L_meta_21763 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12633 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21763.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21763.Helpers.witness]
