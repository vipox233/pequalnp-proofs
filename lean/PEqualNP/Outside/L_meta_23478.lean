import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23478

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.or, [5, 9]⟩,
    ⟨GateOp.not, [10, 10]⟩,
    ⟨GateOp.and, [6, 11]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23478

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23478 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (917 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23478.circuit, PEqualNP.Outside.L_meta_23478.shape, by decide, by decide +kernel⟩
