import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22442

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [8, 3]⟩,
    ⟨GateOp.or, [5, 1]⟩,
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.or, [13, 7]⟩,
    ⟨GateOp.or, [2, 11]⟩,
    ⟨GateOp.or, [11, 9]⟩,
    ⟨GateOp.and, [13, 17]⟩,
    ⟨GateOp.or, [14, 4]⟩,
    ⟨GateOp.or, [16, 15]⟩,
    ⟨GateOp.and, [20, 19]⟩,
    ⟨GateOp.or, [21, 18]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22442

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22442 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881907 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22442.circuit, PEqualNP.Outside.L_meta_22442.shape, by decide,
    by decide +kernel⟩
