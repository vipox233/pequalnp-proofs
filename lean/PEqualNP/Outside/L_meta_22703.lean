import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22703

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [7, 6]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [8, 0]⟩,
    ⟨GateOp.or, [12, 3]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 14]⟩,
    ⟨GateOp.and, [11, 0]⟩,
    ⟨GateOp.or, [13, 1]⟩,
    ⟨GateOp.and, [17, 4]⟩,
    ⟨GateOp.or, [13, 10]⟩,
    ⟨GateOp.and, [15, 19]⟩,
    ⟨GateOp.or, [16, 18]⟩,
    ⟨GateOp.or, [21, 20]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22703

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22703 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903023 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22703.circuit, PEqualNP.Outside.L_meta_22703.shape, by decide,
    by decide +kernel⟩
