import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21297

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [8, 7]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.or, [10, 1]⟩,
    ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.and, [4, 3]⟩,
    ⟨GateOp.or, [5, 0]⟩,
    ⟨GateOp.and, [12, 14]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.and, [16, 11]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [15, 18]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21297

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21297 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40797 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21297.circuit, PEqualNP.Outside.L_meta_21297.shape, by decide,
    by decide +kernel⟩
