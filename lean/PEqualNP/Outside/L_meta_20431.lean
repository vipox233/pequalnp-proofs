import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20431

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 0]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [8, 12]⟩,
    ⟨GateOp.not, [14]⟩,
    ⟨GateOp.and, [13, 15]⟩,
    ⟨GateOp.and, [14, 11]⟩,
    ⟨GateOp.or, [17, 16]⟩]
  output := 18

theorem fanIn : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_20431

theorem PEqualNP.Outside.L_meta_20431 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7374937 : ℕ).testBit (5 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_20431.circuit, PEqualNP.Outside.L_meta_20431.fanIn, by decide, by decide⟩
