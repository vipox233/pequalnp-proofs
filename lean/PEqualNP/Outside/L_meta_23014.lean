import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23014.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 7-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23014.Helpers

theorem PEqualNP.Outside.L_meta_23014 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4427327 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23014.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_23014.Helpers.witness]
