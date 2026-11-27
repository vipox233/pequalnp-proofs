import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22218.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.or, [8, 15]⟩, ⟨GateOp.and, [9, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22218.Helpers

theorem PEqualNP.Outside.L_meta_22218 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22218.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22218.Helpers.witness]
