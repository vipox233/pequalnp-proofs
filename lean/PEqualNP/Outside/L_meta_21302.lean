import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21302

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.or, [1, 0]⟩,
    ⟨GateOp.or, [1, 7]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.or, [10, 2]⟩,
    ⟨GateOp.and, [15, 14]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.and, [17, 12]⟩,
    ⟨GateOp.or, [18, 16]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21302

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21302 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47870 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21302.circuit, PEqualNP.Outside.L_meta_21302.shape, by decide,
    by decide +kernel⟩
