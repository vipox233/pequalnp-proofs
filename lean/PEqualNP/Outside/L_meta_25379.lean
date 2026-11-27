import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25379.Helpers

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨GateOp.not, [5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [3, 6]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [10, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25379.Helpers

theorem PEqualNP.Outside.L_meta_25379 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374839 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25379.Helpers.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_25379.Helpers.witness]
