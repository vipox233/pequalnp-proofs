import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22304.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [14, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_22304.Helpers

theorem PEqualNP.Outside.L_meta_22304 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22304.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22304.Helpers.witness]
