import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21337

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.and, [9, 11]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [13, 10]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [17, 16]⟩,
    ⟨GateOp.or, [12, 18]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21337

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21337 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106269 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21337.circuit, PEqualNP.Outside.L_meta_21337.shape, by decide,
    by decide +kernel⟩
