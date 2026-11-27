import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21945.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [3, 5]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [2, 12]⟩, ⟨GateOp.or, [9, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21945.Helpers

theorem PEqualNP.Outside.L_meta_21945 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20287 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21945.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21945.Helpers.witness]
