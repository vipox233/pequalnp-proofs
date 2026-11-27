import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21935.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [11, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21935.Helpers

theorem PEqualNP.Outside.L_meta_21935 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21935.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_21935.Helpers.witness]
