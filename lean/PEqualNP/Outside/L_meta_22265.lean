import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22265.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [6, 11]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [2, 14]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22265.Helpers

theorem PEqualNP.Outside.L_meta_22265 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18364 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22265.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22265.Helpers.witness]
