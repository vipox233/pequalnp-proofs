import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22551.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 8-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [7, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_22551.Helpers

theorem PEqualNP.Outside.L_meta_22551 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33587 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22551.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22551.Helpers.witness]
