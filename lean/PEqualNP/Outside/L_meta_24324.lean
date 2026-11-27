import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_24324 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4443839 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨{ gates := [⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 11]⟩], output := 12 }, ?_, ?_, ?_⟩
  · letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    unfold PEqualNP.MetaComplexity.FanInTwo
    decide
  · decide
  · decide +kernel
