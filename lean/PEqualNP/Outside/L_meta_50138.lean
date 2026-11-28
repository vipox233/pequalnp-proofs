import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50138

/-- An explicit fan-in-two circuit with 6 gates found by exhaustive search; wires 0 to 3 are the
thresholds, wires 4 and 5 the constants. -/
def circ : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩], 0⟩

end PEqualNP.Outside.L_meta_50138

open PEqualNP.Outside.L_meta_50138 in
theorem PEqualNP.Outside.L_meta_50138 :
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
      PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
      ∀ t : Fin 6,
        let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
        let w := D.wires xs
        w.getD p.val false = (14 : Nat).testBit t.val ∧
        w.getD q.val false = (40 : Nat).testBit t.val ∧
        w.getD r.val false = (52 : Nat).testBit t.val := by
  refine ⟨circ, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ?_, by decide, by decide, by decide, by decide⟩
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
