import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23856

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.not, [7, 7]⟩,
    ⟨GateOp.and, [6, 9]⟩,
    ⟨GateOp.or, [8, 10]⟩]
  output := 11

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23856

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23856 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4495 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23856.circuit, PEqualNP.Outside.L_meta_23856.shape, by decide, by decide +kernel⟩
