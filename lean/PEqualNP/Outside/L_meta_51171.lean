import PEqualNP.Defs
import Mathlib.Tactic.IntervalCases

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_51171
private def circuit : Circuit := ⟨[⟨.not, [1]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [8, 0]⟩, ⟨.not, [8]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [11, 2]⟩], 0⟩
end PEqualNP.Outside.L_meta_51171

open PEqualNP.Outside.L_meta_51171 in
theorem PEqualNP.Outside.L_meta_51171 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (40 : Nat).testBit t.val ∧
    w.getD q.val false = (44 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val := by
  refine ⟨circuit, ⟨12, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, ?_, ?_, by decide, by decide, ?_⟩
  · simp [FanInTwo, circuit]
  · intro j hj
    change j < 6 at hj
    interval_cases j <;> decide
  · decide +kernel
