import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_49986

/-- An explicit fan-in-two circuit with 5 gates found by exhaustive search; wires 0 to 3 are the
thresholds, wires 4 and 5 the constants. -/
def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩], 0⟩

end PEqualNP.Outside.L_meta_49986

open PEqualNP.Outside.L_meta_49986 in
theorem PEqualNP.Outside.L_meta_49986 :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
      ∀ t : Fin 5,
        let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (4 : Nat).testBit t.val ∧
        w.getD q.val false = (19 : Nat).testBit t.val ∧
        w.getD r.val false = (26 : Nat).testBit t.val := by
  refine ⟨circ, ⟨10, by decide⟩, ⟨9, by decide⟩, ⟨8, by decide⟩, ?_, by decide, by decide, by decide, by decide⟩
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
