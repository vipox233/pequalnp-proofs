import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22714

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [4, 1]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [2, 11]⟩,
    ⟨GateOp.or, [7, 6]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [12, 9]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.and, [9, 0]⟩,
    ⟨GateOp.or, [17, 14]⟩,
    ⟨GateOp.and, [18, 15]⟩,
    ⟨GateOp.or, [3, 13]⟩,
    ⟨GateOp.and, [16, 20]⟩,
    ⟨GateOp.or, [19, 21]⟩]
  output := 22

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22714

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22714 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908221 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22714.circuit, PEqualNP.Outside.L_meta_22714.shape, by decide,
    by decide +kernel⟩
