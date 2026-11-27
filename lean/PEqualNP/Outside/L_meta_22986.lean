import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22986.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 6-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [9, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_22986.Helpers

theorem PEqualNP.Outside.L_meta_22986 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22986.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22986.Helpers.witness]
