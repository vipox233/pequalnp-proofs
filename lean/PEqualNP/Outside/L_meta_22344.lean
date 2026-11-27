import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22344.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 14-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [4, 7]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.not, [16]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [12, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_22344.Helpers

theorem PEqualNP.Outside.L_meta_22344 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16538 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22344.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22344.Helpers.witness]
