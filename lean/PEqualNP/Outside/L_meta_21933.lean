import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21933.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21933.Helpers

theorem PEqualNP.Outside.L_meta_21933 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33590 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21933.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21933.Helpers.witness]
