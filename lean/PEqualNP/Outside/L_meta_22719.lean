import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22719

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [4, 10]⟩,
    ⟨GateOp.or, [9, 3]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.or, [13, 5]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.or, [8, 14]⟩,
    ⟨GateOp.and, [12, 5]⟩,
    ⟨GateOp.or, [4, 14]⟩,
    ⟨GateOp.or, [12, 16]⟩,
    ⟨GateOp.and, [11, 19]⟩,
    ⟨GateOp.and, [15, 18]⟩,
    ⟨GateOp.or, [21, 17]⟩,
    ⟨GateOp.or, [22, 20]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22719

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22719 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881466 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22719.circuit, PEqualNP.Outside.L_meta_22719.shape, by decide,
    by decide +kernel⟩
