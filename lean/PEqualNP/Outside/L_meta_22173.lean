import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22173.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.and, [6, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [4, 12]⟩, ⟨GateOp.and, [7, 13]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [11, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22173.Helpers

theorem PEqualNP.Outside.L_meta_22173 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16907 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22173.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22173.Helpers.witness]
