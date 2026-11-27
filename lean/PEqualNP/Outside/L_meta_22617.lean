import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22617

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [8, 5]⟩,
    ⟨GateOp.or, [12, 9]⟩,
    ⟨GateOp.or, [3, 11]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.or, [10, 14]⟩,
    ⟨GateOp.and, [15, 10]⟩,
    ⟨GateOp.and, [0, 13]⟩,
    ⟨GateOp.or, [5, 16]⟩,
    ⟨GateOp.or, [4, 2]⟩,
    ⟨GateOp.and, [19, 20]⟩,
    ⟨GateOp.or, [21, 18]⟩,
    ⟨GateOp.or, [22, 17]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22617

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22617 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (323067 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22617.circuit, PEqualNP.Outside.L_meta_22617.shape, by decide,
    by decide +kernel⟩
