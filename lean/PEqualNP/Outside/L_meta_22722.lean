import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22722

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [9, 2]⟩,
    ⟨GateOp.or, [5, 1]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [13, 7]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [11, 10]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.and, [20, 18]⟩,
    ⟨GateOp.and, [19, 17]⟩,
    ⟨GateOp.or, [22, 21]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22722

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22722 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881970 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22722.circuit, PEqualNP.Outside.L_meta_22722.shape, by decide,
    by decide +kernel⟩
