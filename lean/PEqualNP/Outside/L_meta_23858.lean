import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23858

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.not, [8, 8]⟩,
    ⟨GateOp.and, [5, 9]⟩,
    ⟨GateOp.or, [6, 10]⟩]
  output := 11

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23858

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23858 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4503 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23858.circuit, PEqualNP.Outside.L_meta_23858.shape, by decide, by decide +kernel⟩
