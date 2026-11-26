import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20649
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates := [⟨GateOp.and, [3, 5]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [11, 7]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.and, [4, 13]⟩, ⟨GateOp.or, [10, 14]⟩],
    output := 15 }

end PEqualNP.Outside.L_meta_20649

theorem PEqualNP.Outside.L_meta_20649 :
    (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15761408 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  refine ⟨PEqualNP.Outside.L_meta_20649.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20649.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
