import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21949.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21949.Helpers

theorem PEqualNP.Outside.L_meta_21949 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33590 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21949.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21949.Helpers.witness]
