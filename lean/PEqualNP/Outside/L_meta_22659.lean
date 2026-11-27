import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22659

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [7, 6]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [10, 4]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [9, 13]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.or, [16, 14]⟩,
    ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.and, [15, 17]⟩,
    ⟨GateOp.and, [12, 2]⟩,
    ⟨GateOp.or, [19, 20]⟩,
    ⟨GateOp.and, [1, 18]⟩,
    ⟨GateOp.or, [21, 22]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22659

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22659 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841148 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22659.circuit, PEqualNP.Outside.L_meta_22659.shape, by decide,
    by decide +kernel⟩
