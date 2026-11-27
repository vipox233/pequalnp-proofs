import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21889

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [7, 9]⟩]
  output := 10

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21889

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21889 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (788 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21889.circuit, PEqualNP.Outside.L_meta_21889.shape, by decide, by decide +kernel⟩
