import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22620

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [1]⟩,
    ⟨GateOp.and, [3, 6]⟩,
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.and, [4, 8]⟩,
    ⟨GateOp.and, [2, 1]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.or, [11, 9]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.not, [13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22620

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22620 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17047 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22620.circuit, PEqualNP.Outside.L_meta_22620.shape, by decide, by decide +kernel⟩
