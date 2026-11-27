import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21957.Helpers

open PEqualNP.CircuitLowerBounds

/-- A 9-gate circuit found by SAT-based exact synthesis: inputs 0..5 are the vertices; the statement turns on the two vertices of a pair (one when i = j);
gate `j` writes wire `6 + j`, the output is the last gate. -/
def witness : Circuit :=
  ⟨[⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [8, 11]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.and, [11, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_21957.Helpers

theorem PEqualNP.Outside.L_meta_21957 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33725 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21957.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_21957.Helpers.witness]
