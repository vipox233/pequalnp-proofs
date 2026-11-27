import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22467.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 16-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.not, [19]⟩, ⟨GateOp.or, [11, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_22467.Helpers

theorem PEqualNP.Outside.L_meta_22467 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 16 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16568 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22467.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22467.Helpers.witness]
