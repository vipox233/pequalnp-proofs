import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22715

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [9, 6]⟩,
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [2, 5]⟩,
    ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.or, [1, 0]⟩,
    ⟨GateOp.or, [14, 12]⟩,
    ⟨GateOp.and, [12, 14]⟩,
    ⟨GateOp.or, [3, 16]⟩,
    ⟨GateOp.and, [15, 11]⟩,
    ⟨GateOp.and, [18, 13]⟩,
    ⟨GateOp.or, [4, 17]⟩,
    ⟨GateOp.or, [21, 20]⟩,
    ⟨GateOp.or, [19, 22]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22715

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22715 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908279 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22715.circuit, PEqualNP.Outside.L_meta_22715.shape, by decide,
    by decide +kernel⟩
