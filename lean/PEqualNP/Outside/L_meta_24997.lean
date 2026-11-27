import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24997

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.or, [4, 10]⟩,
    ⟨GateOp.and, [6, 11]⟩,
    ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.not, [13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24997

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24997 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549909 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24997.circuit, PEqualNP.Outside.L_meta_24997.shape, by decide, by decide +kernel⟩
