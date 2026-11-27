import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21961.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.and, [7, 12]⟩, ⟨GateOp.or, [9, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21961.Helpers

theorem PEqualNP.Outside.L_meta_21961 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33958 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21961.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21961.Helpers.witness]
