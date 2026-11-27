import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22106.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 11-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.and, [10, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_22106.Helpers

theorem PEqualNP.Outside.L_meta_22106 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17334 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22106.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22106.Helpers.witness]
