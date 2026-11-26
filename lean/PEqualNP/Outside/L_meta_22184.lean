import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22184

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 0]⟩,
    ⟨GateOp.and, [9, 0]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [4, 1]⟩,
    ⟨GateOp.or, [13, 10]⟩,
    ⟨GateOp.or, [14, 5]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.or, [12, 6]⟩,
    ⟨GateOp.or, [10, 8]⟩,
    ⟨GateOp.and, [15, 17]⟩,
    ⟨GateOp.and, [16, 18]⟩,
    ⟨GateOp.or, [20, 19]⟩]
  output := 21

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22184

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22184 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841517 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_22184.circuit, PEqualNP.Outside.L_meta_22184.shape, by decide,
    by decide +kernel⟩
