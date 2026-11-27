import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22149.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.not, [0]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.and, [7, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.and, [6, 14]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.not, [16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22149.Helpers

theorem PEqualNP.Outside.L_meta_22149 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16571 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22149.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22149.Helpers.witness]
