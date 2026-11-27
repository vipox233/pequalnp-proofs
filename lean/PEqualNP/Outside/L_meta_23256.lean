import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23256

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.not, [8, 8]⟩,
    ⟨GateOp.or, [6, 9]⟩]
  output := 10

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23256

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23256 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147216 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23256.circuit, PEqualNP.Outside.L_meta_23256.shape, by decide, by decide +kernel⟩
