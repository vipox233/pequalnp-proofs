import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21498_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.or, [7, 5]⟩, ⟨GateOp.not, [8]⟩], 9⟩

theorem wit_fan : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21498_aux

theorem PEqualNP.Outside.L_meta_21498 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (65 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21498_aux.wit, PEqualNP.Outside.L_meta_21498_aux.wit_fan, by decide, by decide +kernel⟩
