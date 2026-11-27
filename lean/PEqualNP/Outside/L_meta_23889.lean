import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23889

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.not, [6, 6]⟩,
    ⟨GateOp.and, [5, 7]⟩,
    ⟨GateOp.and, [2, 8]⟩,
    ⟨GateOp.or, [9, 10]⟩]
  output := 11

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23889

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23889 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13084 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23889.circuit, PEqualNP.Outside.L_meta_23889.shape, by decide, by decide +kernel⟩
