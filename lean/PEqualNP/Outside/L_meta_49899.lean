import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49899_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[⟨.not, [2]⟩, ⟨.and, [6, 1]⟩, ⟨.not, [7]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [6, 0]⟩, ⟨.and, [8, 0]⟩], 11⟩

end PEqualNP.Outside.L_meta_49899_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_49899 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (20 : Nat).testBit t.val ∧
    w.getD r.val false = (26 : Nat).testBit t.val :=
  ⟨PEqualNP.Outside.L_meta_49899_aux.witness, ⟨10, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩,
    by simp [FanInTwo, PEqualNP.Outside.L_meta_49899_aux.witness], by (first | decide | simp [PEqualNP.Outside.L_meta_49899_aux.witness, ReadsBack, gateAt]),
    by decide, by decide, by decide⟩
