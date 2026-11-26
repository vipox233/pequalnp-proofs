import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22563

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [8, 1]⟩,
    ⟨GateOp.or, [9, 2]⟩,
    ⟨GateOp.or, [10, 6]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.and, [15, 13]⟩,
    ⟨GateOp.and, [14, 11]⟩,
    ⟨GateOp.or, [17, 12]⟩,
    ⟨GateOp.or, [4, 18]⟩,
    ⟨GateOp.and, [16, 19]⟩,
    ⟨GateOp.or, [21, 20]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22563

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22563 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948409 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22563.circuit, PEqualNP.Outside.L_meta_22563.shape, by decide,
    by decide +kernel⟩
