import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22712

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 8]⟩,
    ⟨GateOp.or, [10, 3]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [12, 9]⟩,
    ⟨GateOp.or, [4, 0]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.or, [2, 13]⟩,
    ⟨GateOp.or, [15, 2]⟩,
    ⟨GateOp.or, [17, 14]⟩,
    ⟨GateOp.or, [1, 14]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.and, [20, 18]⟩,
    ⟨GateOp.and, [16, 19]⟩,
    ⟨GateOp.or, [22, 21]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22712

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22712 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908156 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22712.circuit, PEqualNP.Outside.L_meta_22712.shape, by decide,
    by decide +kernel⟩
