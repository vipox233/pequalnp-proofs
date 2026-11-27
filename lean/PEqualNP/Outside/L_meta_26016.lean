import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26016

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.and, [3, 9]⟩,
    ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.not, [12]⟩], 13⟩

theorem fits : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_26016

theorem PEqualNP.Outside.L_meta_26016 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 15, 12, 3] : List ℕ).getD u.val 0).testBit v.val) C) := by
  exact ⟨PEqualNP.Outside.L_meta_26016.circ, PEqualNP.Outside.L_meta_26016.fits, by decide,
    by decide +kernel, by decide +kernel⟩
