import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_50000

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [⟨GateOp.not, [0]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.not, [7]⟩, ⟨GateOp.and, [1, 8]⟩, ⟨GateOp.or, [3, 8]⟩], output := 10 }

theorem f1 : PEqualNP.MetaComplexity.FanInTwo c1 := by
  intro g hg
  simp only [c1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_50000

theorem PEqualNP.Outside.L_meta_50000 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (22 : Nat).testBit t.val ∧
    w.getD r.val false = (25 : Nat).testBit t.val := by
  refine ⟨PEqualNP.Outside.L_meta_50000.c1, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨7, by decide⟩, PEqualNP.Outside.L_meta_50000.f1, by decide, by decide, by decide, ?_⟩
  decide
