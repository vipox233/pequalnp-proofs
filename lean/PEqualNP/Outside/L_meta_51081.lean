import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

-- A circuit of 6 gates, 2 of them NOT, with wires carrying the outputs 24, 38, 52.
-- Wires 0..4 are the thresholds, 5 is false, 6 is true; each wire is read as a 6-bit number:
-- wire 7 = NOT 2 -> 7, wire 8 = AND 1 7 -> 4, wire 9 = OR 3 8 -> 52, wire 10 = OR 4 7 -> 39, wire 11 = AND 0 10 -> 38, wire 12 = NOT 10 -> 24.
-- Found by exhaustive search over the numbers a gate can add.

namespace PEqualNP.Outside.L_meta_51081

open PEqualNP.CircuitLowerBounds

/-- The circuit. -/
def wit : Circuit := ⟨[⟨GateOp.not, [2]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.not, [10]⟩], 0⟩

end PEqualNP.Outside.L_meta_51081

theorem PEqualNP.Outside.L_meta_51081 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (24 : Nat).testBit t.val ∧
    w.getD q.val false = (38 : Nat).testBit t.val ∧
    w.getD r.val false = (52 : Nat).testBit t.val :=
  ⟨PEqualNP.Outside.L_meta_51081.wit, ⟨12, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩,
    by simp [PEqualNP.Outside.L_meta_51081.wit, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide, by decide, by decide⟩
