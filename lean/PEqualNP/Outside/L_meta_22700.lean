import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22700

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [9, 2]⟩,
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [7, 12]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [15, 13]⟩,
    ⟨GateOp.or, [14, 18]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.and, [5, 3]⟩,
    ⟨GateOp.and, [20, 19]⟩,
    ⟨GateOp.or, [22, 21]⟩]
  output := 23

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22700

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22700 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851322 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22700.circuit, PEqualNP.Outside.L_meta_22700.shape, by decide,
    by decide +kernel⟩
