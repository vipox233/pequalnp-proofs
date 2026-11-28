import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

theorem PEqualNP.Outside.L_meta_49863 : (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (21 : Nat).testBit t.val ∧
    w.getD r.val false = (25 : Nat).testBit t.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [8, 1]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [10, 3]⟩], 11⟩,
    ⟨7, by decide⟩, ⟨11, by decide⟩, ⟨8, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack
    decide
  · decide
  · decide
  · decide
