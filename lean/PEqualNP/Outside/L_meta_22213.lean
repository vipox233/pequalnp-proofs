import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22213.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 12-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [12, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_22213.Helpers

theorem PEqualNP.Outside.L_meta_22213 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17330 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22213.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_22213.Helpers.witness]
