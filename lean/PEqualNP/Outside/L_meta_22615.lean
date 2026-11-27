import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22615

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.or, [10, 0]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.and, [5, 0]⟩,
    ⟨GateOp.or, [9, 13]⟩,
    ⟨GateOp.or, [12, 2]⟩,
    ⟨GateOp.or, [14, 11]⟩,
    ⟨GateOp.or, [13, 18]⟩,
    ⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.and, [16, 11]⟩,
    ⟨GateOp.or, [21, 20]⟩,
    ⟨GateOp.and, [22, 19]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22615

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22615 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321019 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22615.circuit, PEqualNP.Outside.L_meta_22615.shape, by decide,
    by decide +kernel⟩
