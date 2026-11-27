import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22924.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 7-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [7, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_22924.Helpers

theorem PEqualNP.Outside.L_meta_22924 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25374 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22924.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_22924.Helpers.witness]
