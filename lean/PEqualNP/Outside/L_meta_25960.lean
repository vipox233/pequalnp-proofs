import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25960_aux

open PEqualNP.CircuitLowerBounds

def C0 : Circuit :=
  { gates := [⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [4, 8]⟩,
      ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [9, 11]⟩], output := 12 }

end PEqualNP.Outside.L_meta_25960_aux

open PEqualNP.Outside.L_meta_25960_aux in
theorem PEqualNP.Outside.L_meta_25960 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 14, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨C0, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
