import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21938.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_21938.Helpers

theorem PEqualNP.Outside.L_meta_21938 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33598 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21938.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21938.Helpers.witness]
