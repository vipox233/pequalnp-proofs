import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21312

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [11, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩,
    ⟨GateOp.and, [10, 2]⟩,
    ⟨GateOp.or, [5, 14]⟩,
    ⟨GateOp.or, [15, 12]⟩,
    ⟨GateOp.or, [13, 8]⟩,
    ⟨GateOp.or, [16, 0]⟩,
    ⟨GateOp.and, [18, 17]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21312

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21312 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103773 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21312.circuit, PEqualNP.Outside.L_meta_21312.shape, by decide,
    by decide +kernel⟩
