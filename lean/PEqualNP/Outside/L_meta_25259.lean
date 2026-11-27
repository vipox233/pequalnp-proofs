import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25259_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [5]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [0, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [8, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25259_aux

theorem PEqualNP.Outside.L_meta_25259 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50862 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25259_aux.wit, PEqualNP.Outside.L_meta_25259_aux.wit_p, by decide, by decide +kernel⟩
