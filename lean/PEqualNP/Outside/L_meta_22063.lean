import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22063

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.not, [6]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.not, [10]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [8, 12]⟩,
    ⟨GateOp.or, [14, 13]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22063

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22063 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33971 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22063.circuit, PEqualNP.Outside.L_meta_22063.shape, by decide, by decide +kernel⟩
