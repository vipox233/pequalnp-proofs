import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24106.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 10-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 6]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [5, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24106.Helpers

theorem PEqualNP.Outside.L_meta_24106 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4444 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24106.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24106.Helpers.witness]
