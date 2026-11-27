import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22561

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [9, 6]⟩,
    ⟨GateOp.or, [5, 13]⟩,
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.and, [11, 10]⟩,
    ⟨GateOp.and, [0, 16]⟩,
    ⟨GateOp.or, [18, 17]⟩,
    ⟨GateOp.and, [15, 12]⟩,
    ⟨GateOp.or, [19, 20]⟩,
    ⟨GateOp.or, [21, 4]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22561

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22561 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947645 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22561.circuit, PEqualNP.Outside.L_meta_22561.shape, by decide,
    by decide +kernel⟩
