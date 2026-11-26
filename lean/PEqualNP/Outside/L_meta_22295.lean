import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22295

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 1]⟩,
    ⟨GateOp.and, [6, 0]⟩,
    ⟨GateOp.or, [7, 0]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.or, [4, 2]⟩,
    ⟨GateOp.or, [15, 8]⟩,
    ⟨GateOp.or, [16, 9]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 5]⟩,
    ⟨GateOp.and, [13, 19]⟩,
    ⟨GateOp.and, [17, 18]⟩,
    ⟨GateOp.or, [20, 21]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22295

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22295 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (838775 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22295.circuit, PEqualNP.Outside.L_meta_22295.shape, by decide,
    by decide +kernel⟩
