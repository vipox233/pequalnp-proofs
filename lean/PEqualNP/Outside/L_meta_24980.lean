import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24980

open PEqualNP.CircuitLowerBounds

def circ : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [3, 9]⟩,
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.and, [2, 11]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [8, 13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24980

theorem PEqualNP.Outside.L_meta_24980 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6475580 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24980.circ, PEqualNP.Outside.L_meta_24980.shape, by decide, by decide +kernel⟩
