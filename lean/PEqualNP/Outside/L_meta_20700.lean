import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20700
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates := [⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [10, 7]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [4, 15]⟩, ⟨GateOp.or, [14, 16]⟩],
    output := 17 }

end PEqualNP.Outside.L_meta_20700

theorem PEqualNP.Outside.L_meta_20700 :
    (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25398272 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  refine ⟨PEqualNP.Outside.L_meta_20700.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20700.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
