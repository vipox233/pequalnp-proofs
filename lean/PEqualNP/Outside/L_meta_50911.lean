import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50911

open PEqualNP.CircuitLowerBounds

-- The first wires are the thresholds x_i = [i < t], then false and true; gate j writes the next wire.
-- Found by an exhaustive search over the masks of the wires on all values of t.
def circuit : Circuit := ⟨[⟨.not, [2]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [0, 10]⟩, ⟨.not, [10]⟩], 0⟩

end PEqualNP.Outside.L_meta_50911

theorem PEqualNP.Outside.L_meta_50911 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (8 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val := by
  refine ⟨PEqualNP.Outside.L_meta_50911.circuit, ⟨12, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    simp only [PEqualNP.Outside.L_meta_50911.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
  · decide
  · decide
