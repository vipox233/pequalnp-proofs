import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24588

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [2, 7]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.and, [8, 10]⟩,
    ⟨GateOp.or, [5, 11]⟩,
    ⟨GateOp.not, [12]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24588

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24588 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549401 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24588.circuit, PEqualNP.Outside.L_meta_24588.shape, by decide, by decide +kernel⟩
