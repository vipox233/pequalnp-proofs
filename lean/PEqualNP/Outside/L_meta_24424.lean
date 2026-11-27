import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24424

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.and, [9, 11]⟩,
    ⟨GateOp.or, [7, 12]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24424

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24424 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52278 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24424.circuit, PEqualNP.Outside.L_meta_24424.shape, by decide, by decide +kernel⟩
