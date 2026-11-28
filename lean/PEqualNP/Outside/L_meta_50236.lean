import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50236_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.not, [2]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [7, 0]⟩, ⟨.not, [8]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [8, 1]⟩], 12⟩

end PEqualNP.Outside.L_meta_50236_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_50236 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (52 : Nat).testBit t.val :=
  ⟨PEqualNP.Outside.L_meta_50236_aux.witness, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩,
    by simp [FanInTwo, PEqualNP.Outside.L_meta_50236_aux.witness], by (first | decide | simp [PEqualNP.Outside.L_meta_50236_aux.witness, ReadsBack, gateAt]),
    by decide, by decide, by decide⟩
