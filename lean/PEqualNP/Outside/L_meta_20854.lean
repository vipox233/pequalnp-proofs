import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20854
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates := [⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.or, [17, 18]⟩],
    output := 19 }

end PEqualNP.Outside.L_meta_20854

theorem PEqualNP.Outside.L_meta_20854 :
    (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27004993 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  refine ⟨PEqualNP.Outside.L_meta_20854.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20854.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
