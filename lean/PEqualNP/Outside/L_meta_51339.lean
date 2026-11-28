import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_51339 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (50 : Nat).testBit t.val := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 11]⟩], 0⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨9, by decide⟩, ?_, ?_, by decide, by decide, by decide⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · unfold PEqualNP.MetaComplexity.NestedCover.ReadsBack PEqualNP.MetaComplexity.NestedCover.gateAt
    decide
