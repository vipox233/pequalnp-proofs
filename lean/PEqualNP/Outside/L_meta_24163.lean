import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24163_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.and, [0, 10]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [5, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24163_aux

theorem PEqualNP.Outside.L_meta_24163 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266972 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24163_aux.wit, PEqualNP.Outside.L_meta_24163_aux.wit_p, by decide, by decide +kernel⟩
