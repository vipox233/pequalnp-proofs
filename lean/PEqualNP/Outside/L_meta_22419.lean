import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22419

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [6, 2]⟩,
    ⟨GateOp.or, [4, 0]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.and, [11, 10]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [13, 16]⟩,
    ⟨GateOp.and, [17, 12]⟩,
    ⟨GateOp.or, [16, 4]⟩,
    ⟨GateOp.or, [18, 15]⟩,
    ⟨GateOp.and, [14, 19]⟩,
    ⟨GateOp.or, [21, 20]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22419

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22419 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1880946 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22419.circuit, PEqualNP.Outside.L_meta_22419.shape, by decide,
    by decide +kernel⟩
