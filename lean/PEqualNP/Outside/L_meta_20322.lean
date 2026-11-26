import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20322

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [14, 7]⟩,
    ⟨GateOp.or, [11, 1]⟩,
    ⟨GateOp.or, [9, 6]⟩,
    ⟨GateOp.or, [0, 13]⟩,
    ⟨GateOp.or, [18, 2]⟩,
    ⟨GateOp.or, [16, 18]⟩,
    ⟨GateOp.or, [20, 15]⟩,
    ⟨GateOp.or, [17, 15]⟩,
    ⟨GateOp.or, [4, 7]⟩,
    ⟨GateOp.or, [23, 24]⟩,
    ⟨GateOp.or, [10, 3]⟩,
    ⟨GateOp.or, [14, 19]⟩,
    ⟨GateOp.or, [20, 4]⟩,
    ⟨GateOp.or, [22, 19]⟩,
    ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.and, [21, 25]⟩,
    ⟨GateOp.and, [25, 30]⟩,
    ⟨GateOp.or, [23, 30]⟩,
    ⟨GateOp.or, [28, 26]⟩,
    ⟨GateOp.or, [34, 11]⟩,
    ⟨GateOp.or, [32, 27]⟩,
    ⟨GateOp.or, [33, 2]⟩,
    ⟨GateOp.and, [36, 37]⟩,
    ⟨GateOp.or, [31, 12]⟩,
    ⟨GateOp.and, [39, 35]⟩,
    ⟨GateOp.and, [26, 29]⟩,
    ⟨GateOp.or, [41, 40]⟩,
    ⟨GateOp.or, [42, 38]⟩]
  output := 43

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_20322

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_20322 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1125029453109683085 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨PEqualNP.Outside.L_meta_20322.circuit, PEqualNP.Outside.L_meta_20322.shape, by decide,
    by decide +kernel⟩
