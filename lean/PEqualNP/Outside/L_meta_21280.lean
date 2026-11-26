import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21280

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [4, 1]⟩,
    ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.or, [7, 5]⟩,
    ⟨GateOp.or, [5, 9]⟩,
    ⟨GateOp.or, [10, 0]⟩,
    ⟨GateOp.or, [12, 3]⟩,
    ⟨GateOp.and, [15, 14]⟩,
    ⟨GateOp.or, [11, 8]⟩,
    ⟨GateOp.and, [13, 17]⟩,
    ⟨GateOp.or, [18, 16]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21280

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21280 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39387 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21280.circuit, PEqualNP.Outside.L_meta_21280.shape, by decide,
    by decide +kernel⟩
