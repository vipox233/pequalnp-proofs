import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25417

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.or, [5, 2]⟩,
    ⟨GateOp.or, [2, 0]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.and, [6, 1]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.and, [9, 7]⟩,
    ⟨GateOp.not, [12, 12]⟩,
    ⟨GateOp.and, [11, 13]⟩,
    ⟨GateOp.or, [10, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25417

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25417 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6508095 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25417.circuit, PEqualNP.Outside.L_meta_25417.shape, by decide, by decide +kernel⟩
