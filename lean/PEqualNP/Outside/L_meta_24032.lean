import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24032.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24032.Helpers

theorem PEqualNP.Outside.L_meta_24032 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4185 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24032.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24032.Helpers.witness]
