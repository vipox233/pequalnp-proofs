import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22134.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [11, 14]⟩, ⟨GateOp.and, [13, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22134.Helpers

theorem PEqualNP.Outside.L_meta_22134 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33677 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22134.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22134.Helpers.witness]
