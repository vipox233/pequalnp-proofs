import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24038.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.and, [5, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [10, 12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24038.Helpers

theorem PEqualNP.Outside.L_meta_24038 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4430 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24038.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24038.Helpers.witness]
