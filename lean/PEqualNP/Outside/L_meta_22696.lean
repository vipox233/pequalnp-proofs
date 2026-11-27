import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22696

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.or, [7, 6]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.or, [11, 8]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [13, 12]⟩,
    ⟨GateOp.and, [10, 14]⟩,
    ⟨GateOp.and, [11, 2]⟩,
    ⟨GateOp.or, [13, 12]⟩,
    ⟨GateOp.or, [16, 15]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [20, 17]⟩,
    ⟨GateOp.and, [18, 21]⟩,
    ⟨GateOp.or, [19, 22]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22696

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22696 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849788 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22696.circuit, PEqualNP.Outside.L_meta_22696.shape, by decide,
    by decide +kernel⟩
