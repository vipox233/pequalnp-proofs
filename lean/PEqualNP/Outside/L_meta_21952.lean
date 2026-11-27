import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21952.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [9, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21952.Helpers

theorem PEqualNP.Outside.L_meta_21952 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33687 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21952.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21952.Helpers.witness]
