import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21344

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [7, 1]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.or, [8, 2]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [9, 5]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.and, [15, 11]⟩,
    ⟨GateOp.or, [4, 16]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [17, 18]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21344

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21344 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112315 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21344.circuit, PEqualNP.Outside.L_meta_21344.shape, by decide,
    by decide +kernel⟩
