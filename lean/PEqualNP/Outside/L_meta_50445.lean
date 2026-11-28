import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_50445

def D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 10]⟩], 0⟩

theorem fan : PEqualNP.MetaComplexity.FanInTwo D := by
  intro g hg
  simp only [D, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_50445

theorem PEqualNP.Outside.L_meta_50445 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (36 : Nat).testBit t.val ∧
    w.getD q.val false = (52 : Nat).testBit t.val ∧
    w.getD r.val false = (58 : Nat).testBit t.val := by
  refine ⟨PEqualNP.Outside.L_meta_50445.D, ⟨12, by decide⟩, ⟨11, by decide⟩, ⟨9, by decide⟩, PEqualNP.Outside.L_meta_50445.fan, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
