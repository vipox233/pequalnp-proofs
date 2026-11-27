import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23187.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 6-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [0, 10]⟩], 11⟩

end PEqualNP.Outside.L_meta_23187.Helpers

theorem PEqualNP.Outside.L_meta_23187 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16831 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_23187.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_23187.Helpers.witness]
