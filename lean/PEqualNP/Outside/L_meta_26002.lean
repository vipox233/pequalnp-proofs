import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26002

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 6]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [4, 12]⟩], 13⟩

theorem wit_ok : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 11, 7, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨wit, wit_ok, by decide, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_26002

theorem PEqualNP.Outside.L_meta_26002 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 11, 7, 1] : List ℕ).getD u.val 0).testBit v.val) C) :=
  PEqualNP.Outside.L_meta_26002.main_aux
