import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21801.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 13-gate circuit found by SAT-based exact synthesis: inputs 0..4 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `5 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [14, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_21801.Helpers

theorem PEqualNP.Outside.L_meta_21801 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274966 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21801.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21801.Helpers.witness]
