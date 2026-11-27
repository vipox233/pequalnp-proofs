import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25990_aux

open PEqualNP.CircuitLowerBounds

def C0 : Circuit :=
  { gates := [⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [5, 8]⟩,
      ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [9, 11]⟩, ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.not, [13]⟩, ⟨GateOp.or, [12, 14]⟩],
    output := 15 }

end PEqualNP.Outside.L_meta_25990_aux

open PEqualNP.Outside.L_meta_25990_aux in
theorem PEqualNP.Outside.L_meta_25990 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 12, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨C0, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
