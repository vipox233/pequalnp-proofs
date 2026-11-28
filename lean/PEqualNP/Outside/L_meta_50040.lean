import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_50040 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (18 : Nat).testBit t.val ∧
    w.getD r.val false = (26 : Nat).testBit t.val := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 8] }], output := 10 } : PEqualNP.CircuitLowerBounds.Circuit), ⟨9, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ?_, by decide, by decide, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
