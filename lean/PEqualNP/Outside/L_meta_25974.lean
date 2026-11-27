import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25974_aux

open PEqualNP.CircuitLowerBounds

def gates : List Gate :=
  [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [0, 4]⟩,
   ⟨GateOp.and, [10, 9]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [11, 12]⟩]

end PEqualNP.Outside.L_meta_25974_aux

theorem PEqualNP.Outside.L_meta_25974 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 3, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨PEqualNP.Outside.L_meta_25974_aux.gates, 13⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_25974_aux.gates, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
  · decide
