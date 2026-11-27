import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21807.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.and, [5, 9]⟩, ⟨GateOp.and, [7, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_21807.Helpers

theorem PEqualNP.Outside.L_meta_21807 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279261 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21807.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21807.Helpers.witness]
