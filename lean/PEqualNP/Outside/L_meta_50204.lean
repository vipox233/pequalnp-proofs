import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50204_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.not, [3]⟩, ⟨.and, [7, 2]⟩, ⟨.not, [8]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [7, 1]⟩, ⟨.and, [9, 0]⟩], 12⟩

end PEqualNP.Outside.L_meta_50204_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_50204 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val :=
  ⟨PEqualNP.Outside.L_meta_50204_aux.witness, ⟨11, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩,
    by simp [FanInTwo, PEqualNP.Outside.L_meta_50204_aux.witness], by (first | decide | simp [PEqualNP.Outside.L_meta_50204_aux.witness, ReadsBack, gateAt]),
    by decide, by decide, by decide⟩
