import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22648

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.or, [7, 6]⟩,
    ⟨GateOp.and, [11, 3]⟩,
    ⟨GateOp.or, [4, 12]⟩,
    ⟨GateOp.or, [13, 1]⟩,
    ⟨GateOp.or, [11, 10]⟩,
    ⟨GateOp.and, [12, 2]⟩,
    ⟨GateOp.and, [16, 15]⟩,
    ⟨GateOp.or, [17, 18]⟩,
    ⟨GateOp.or, [9, 8]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.and, [21, 0]⟩,
    ⟨GateOp.or, [19, 22]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22648

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22648 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837117 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22648.circuit, PEqualNP.Outside.L_meta_22648.shape, by decide,
    by decide +kernel⟩
