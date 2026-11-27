import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22290

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [8, 2]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.or, [11, 9]⟩,
    ⟨GateOp.or, [10, 4]⟩,
    ⟨GateOp.or, [11, 3]⟩,
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.and, [12, 13]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [13, 12]⟩,
    ⟨GateOp.and, [18, 15]⟩,
    ⟨GateOp.or, [17, 16]⟩,
    ⟨GateOp.and, [20, 14]⟩,
    ⟨GateOp.or, [21, 19]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22290

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22290 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837113 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22290.circuit, PEqualNP.Outside.L_meta_22290.shape, by decide,
    by decide +kernel⟩
